{-# OPTIONS --no-positivity-check  #-}

module Open3 where
open import Data.Unit
-- open import Logic
import Data.Nat as Nat
open import Data.Function
open Nat 
open import Data.Bool
open import Data.List
open import Data.Product
open import Data.Empty
open import Data.Sum
open import List1
import Data.Vec1 as Vec1
open Vec1 hiding (lookup)
open import HList
open import Data.Maybe

postulate Tag : Set
{-# BUILTIN STRING Tag #-}
Enumeration = List Tag

-- Member of an enumeration
data Member (ts : Enumeration) : Set where
  member : (t : Tag) -> t ∈ ts -> Member ts

data Case1 (A : Set1) : Set1 where
  _↦_ : Tag -> A -> Case1 A

tagOf1 : {A : Set1} -> Case1 A -> Tag
tagOf1 (t ↦ _) = t

data Table1 (A : Set1) : Enumeration -> Set1 where
  [] : Table1 A []
  _∷_ : forall {ts} -> (c : Case1 A) -> Table1 A ts -> Table1 A (tagOf1 c ∷ ts)
infixr 5 _∷_

lookup1 : forall {A ts} -> Table1 A ts -> Member ts -> A
lookup1 [] (member _ ())
lookup1 ((.t ↦ v) ∷ tbl) (member t here)    = v
lookup1 ((_  ↦ v) ∷ tbl) (member t (there p)) = lookup1 tbl (member t p)



data Leaf : Set1 where
  rec : Leaf
  dat : (A : Set) -> Leaf
  


Prod : Set1
Prod = List1 Leaf

countRec : Prod -> ℕ
countRec [] = 0
countRec (rec ∷ l) = 1 + countRec l
countRec (dat _ ∷ l) = countRec l

Code : Enumeration -> Set1
Code tags = Table1 Prod tags

l2s : Set -> Leaf -> Set 
l2s r rec = r
l2s r (dat a) = a

p2s : Set -> Prod -> Set
p2s _ [] = ⊤
p2s r (c ∷ s) = l2s r c × p2s r s

c2s : {Tags : ?} -> Set -> Code Tags -> Set
c2s r [] = ⊥
c2s r ((_ ↦ c) ∷ s) = p2s r c ⊎ c2s r s

-- Semantic of a code is a functor ...
[[_]] : {Tags : ?} -> Code Tags -> Set -> Set
[[ c ]] =  \s -> c2s s c

-- Tying the recursive knot. (hence turning off positivity check...)
data μ {Tags : ?} (C : Code Tags) : Set where
  <_> : [[ C ]] (μ C) -> μ C

primitive primStringEquality : Tag -> Tag -> Bool



data Pattern {Tags : Enumeration} (C : Code Tags) : Set1 where
  _:?_ : (tag : Member Tags) -> (subPatterns : Vec₁ (Pattern C) (countRec (lookup1 C tag))) -> Pattern C
  ?? : Pattern C



mutual 
  matched' : {Tags : Enumeration} {C : Code Tags} -> (X : Set) -> (p : Prod) -> Vec₁ (Pattern C) (countRec p) -> SetList
  matched' X [] [] = []
  matched' X (rec ∷ p) (pat ∷ pats) = List1._++_ (matched X pat) (matched' X p pats)
  matched' X (dat A ∷ p) (pats) = A ∷ matched' X p pats

  matchedT : {Tags0 Tags : Enumeration} {C : Code Tags} {C0 : Code Tags0} -> 
            (X : Set) -> (tag : Member Tags) -> (subPatterns : Vec₁ (Pattern C0) (countRec (lookup1 C tag))) -> SetList
  matchedT {C = C} X tag subPatterns = matched' X (lookup1 C tag) subPatterns 

  matched : {Tags : Enumeration} {C : Code Tags} -> (X : Set) -> Pattern C -> SetList
  matched X ?? = X ∷ []
  matched X (tag :? subPatterns) = matchedT X tag subPatterns


data Maybe1 (A : Set1) : Set1 where
  just    : (x : A) -> Maybe1 A
  nothing : Maybe1 A


_<*>_ : forall {a b} -> Maybe1 (a -> b) -> Maybe1 a -> Maybe1 b
nothing <*> _ = nothing
_ <*> nothing = nothing
just f <*> just a = just (f a)

_<$>_ : forall {a b} -> (a -> b) -> Maybe1 a -> Maybe1 b
f <$> nothing = nothing
f <$> (just x) = just (f x)
infixr 5 _<$>_
infixl 6 _<*>_

mutual 
 extractP : {Tags : Enumeration} {C : Code Tags} -> 
   (X : Set) -> (p : Prod) -> (subPatterns : Vec₁ (Pattern C) (countRec p)) -> p2s (μ C) p -> Maybe1 (HList (matched' p subPatterns))
 extractP [] [] _ = just []
 extractP {C = C} (rec ∷ p) (pat ∷ pats) (c , cs) = just HList._++_  <*> (extract pat c) <*> (extractP p pats cs)
 extractP (dat A ∷ p) (pats) (c , cs) =  just (_∷_ c) <*> (extractP p pats cs)

 extractT : (X : Set) -> {Tags0 Tags : Enumeration} {C0 : Code Tags0} (C : Code Tags) -> 
            (tag : Member Tags) -> (subPatterns : Vec₁ (Pattern C0) (countRec (lookup1 C tag))) -> c2s (μ C0) C -> Maybe1 (HList (matchedT tag subPatterns))
 extractT ((.t ↦ p) ∷ _  ) (member t   here   ) subPatterns (inj₁ content) = extractP p                subPatterns content
 extractT ((.t ↦ p) ∷ _  ) (member t   here   ) subPatterns (inj₂ _)       = nothing
 extractT ((_  ↦ _) ∷ tbl) (member t (there p)) subPatterns (inj₂ content) = extractT tbl (member t p) subPatterns content
 extractT ((_  ↦ _) ∷ tbl) (member t (there p)) subPatterns (inj₁ _)       = nothing
 extractT [] (member _ ()) _ _
 
 extract : (X : Set) -> {Tags : Enumeration} {C : Code Tags} -> (p : Pattern C) -> μ C -> Maybe1 (HList (matched p))
 extract {C = C} (tag :? subPatterns) < v > = extractT C tag subPatterns v
 extract ?? _ = just []
 
data FunCase {Tags : Enumeration} (C : Code Tags) (Result : Set) : Set1 where
  _?->_ : (p : Pattern C) -> (lambdas (matched p) Result) -> FunCase C Result


Function : {Tags : Enumeration} (C : Code Tags) (Result : Set) -> Set1
Function C Result = List1 (FunCase C Result)



-- data Compiled (Result : ResultDesc) where
--     directResult : Result -> Compiled Result
--     analysis : Table (Vec n (Maybe Tag)) (Compiled ModifiedResult) -> Compiled Result

-- case-wise inclusion.
-- _:<_ : Code _ -> Code _ -> Bool
-- _:<_ [] _ = true
-- _:<_ _ [] = false
-- _:<_ (dataCase t _ ∷ s) (dataCase t' _ ∷ s') = primStringEquality t t' ∧ s :< s'
-- _:<_ s (_ ∷ s') = s :< s'


`Val` : Case1 Prod
`Val` = "Val" ↦ (dat ℕ ∷ [])

`Add` : Case1 Prod
`Add` = "Add" ↦ (rec ∷ (rec ∷ []))

`Expr` : Code ?
`Expr` = `Val` ∷ `Add` ∷ [] 




{-# OPTIONS --no-positivity-check #-}
module Path2 where

open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.Vec1
open import Data.Unit hiding (_≤_; _≤?_)
open import Data.Empty
open import Data.Function
import Data.Fin as Fin 
open Fin using (Fin;Fin′;inject;inject';zero;suc;toℕ;less;greater;equal) renaming (_+_ to _+F_)

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality1 hiding (cong)
open import Data.List


{-

module Comment where
 data Funct : Set1 where
  K : (t : Set) -> Funct
  _⊕_ : (l : Funct) -> (r : Funct) -> Funct
  _⊗_ : (l : Funct) -> (r : Funct) -> Funct
  I :  Funct

 [[_]] : Funct -> Set -> Set
 [[ I ]] v = v
 [[ K t ]] v = t
 [[ t1 ⊗ t2 ]] v = [[ t1 ]] v × [[ t2 ]] v
 [[ t1 ⊕ t2 ]] v = [[ t1 ]] v ⊎ [[ t2 ]] v


 path : {a : Set} -> (f : Funct) -> (x : [[ f ]] a) -> Set
 path (K t) x = ⊥
 path (l ⊕ r) (inj₁ x) = path l x
 path (l ⊕ r) (inj₂ y) = path r y
 path (l ⊗ r) (x , y) = path l x ⊎ path r y
 path I x = ⊤

 lookup : {a : Set} -> (f : Funct) -> (x : [[ f ]] a) -> (path f x -> a)
 lookup (K t) x ()
 lookup (l ⊕ r) (inj₁ x) p = lookup l x p
 lookup (l ⊕ r) (inj₂ y) p = lookup r y p
 lookup (l ⊗ r) (x , y) (inj₁ x') = lookup l x x'
 lookup (l ⊗ r) (x , y) (inj₂ y') = lookup r y y'
 lookup I x p = x

-}
data Funct : ℕ -> Set1 where
  μ : forall {n} -> (arg : Funct (1 + n)) -> Funct n
  K : forall {n} -> (t : Set) -> Funct n
  _⊕_ : forall {n} -> (l : Funct n) -> (r : Funct n) -> Funct n
  _⊗_ : forall {n} -> (l : Funct n) -> (r : Funct n) -> Funct n
  π : forall {n} -> (idx : Fin n) -> Funct n

Fun : ℕ -> Set1
Fun 0 = Set
Fun (suc n) = Set -> Fun n

lift2 : {n : ℕ} -> (Set -> Set -> Set) -> Fun n -> Fun n -> Fun n
lift2 {0} _x_ l r = l x r
lift2 {suc n} _x_ l r = \t -> lift2 _x_ (l t) (r t)

consts : (n : ℕ) -> Set -> Fun n
consts 0 s = s
consts (suc n) s = \_ -> consts n s 



data Fix (arg : Set -> Set) : Set where
  In : arg (Fix arg)  -> Fix arg


lift : (n : ℕ) -> (q : (Set -> Set) -> Set) -> Fun (suc n) -> Fun n
lift 0 q s = q s
lift (suc n) q f = \ a -> lift n q (f a)

sem : forall n -> Funct n -> Fun n
sem n (μ arg) = lift _ Fix (sem _ arg)
sem zero (K t) = t
sem (suc n) (K t) = λ t' → sem n (K t)
sem n (l ⊕ r) = lift2 _⊎_ (sem n l) (sem n r)
sem n (l ⊗ r) = lift2 _×_ (sem n l) (sem n r)
sem .(suc n) (π (zero {n})) = consts n
sem .(suc n) (π (suc {n} i)) = λ t → sem n (π i)


[[_]] : forall {n} -> Funct n -> Fun n
[[_]] {n} f = sem n f


_$$_ : forall {n} -> Fun n -> Vec₁ Set n -> Set
f $$ [] = f
f $$ (x ∷ xs) = f x $$ xs

-- Apply all variables
_$!_ : forall {n} -> Funct n -> Vec₁ Set n -> Set
μ arg $! as = Fix (λ r → arg $! (r ∷ as))
K t $! as = t
(l ⊕ r) $! as = l $! as ⊎ r $! as
(l ⊗ r) $! as = l $! as × r $! as
π idx $! as = lookup idx as


-- Apply one variable.
[[_]]$_!_ : forall {n} -> Funct (1 + n) -> (v : Fin (1 + n)) -> Set -> Funct n
[[ μ arg ]]$ v ! x = μ ([[ arg ]]$ suc v ! x)
[[ K t ]]$ v ! x = K t
[[ l ⊕ r ]]$ v ! x = ([[ l ]]$ v ! x) ⊕ ([[ r ]]$ v ! x)
[[ l ⊗ r ]]$ v ! x = ([[ l ]]$ v ! x) ⊕ ([[ r ]]$ v ! x)
[[ π idx ]]$ v ! x with Fin.compare idx v 
[[ π .(inject least) ]]$ v ! x | less .v least = π (inject' least)
[[ π .v ]]$ v ! x | equal .v = K x
[[ π  zero ]]$ ._ ! x | greater .zero ()
[[ π  (suc idx) ]]$ .(inject least) ! x | greater .(suc idx) least  = π idx


path : (f : Funct 1) -> (a : Set) -> (x : f $! (a ∷ [])) -> Set
path (μ arg) a x = {!!}
path (K t) a x = {!!}
path (l ⊕ r) a x = {!!}
path (l ⊗ r) a x = {!!}
path (π idx) a x = {!!}

{-


 
path : (n : ℕ) -> (v : Fin n)  (f : Funct n) -> (as : Vec₁ Set n) -> (x : f $! as) -> Set
path n v (μ arg) as (In x) = path (suc n) (suc v) {!arg $! [[ μ arg ]]!} {!!} {!!} -- ([[ μ arg  ]] ∷ as) x
-- Fix (λ rec → path (suc n) (suc v) arg (Fix (λ r → arg $! (r ∷ as)) ∷ as) x)
path n v (K t) as x = ⊥
path n v (l ⊕ r) as (inj₁ x) = path n v l as x
path n v (l ⊕ r) as (inj₂ y) = path n v r as y
path n v (l ⊗ r) as (x , y) = path n v l as x ⊎ path n v r as y
path n v (π idx) as x with fcompare v idx 
path v _ (π idx) as x | less = lookup idx as -- keep these (because we need to keep recursive positions)
path v _ (π idx) as x | equal = ⊤            -- position we are interested in; keep it.
path v _ (π idx) as x | greater = ⊥          -- treat these as constants

-}

{-

path : (n : ℕ) -> (v : Fin n)  (f : Funct n) -> (as : Vec₁ Set n) -> (x : f $! as) -> Funct (toℕ v)
path n v (μ arg) as (In x) = μ (path (suc n) (suc v) arg ({!!} ∷ as) {!!})
path n v (K t) as x = K ⊥
path n v (l ⊕ r) as x = {!!}
path n v (l ⊗ r) as (x , y) = path n v l as x ⊕ path n v r as y
path n v (π idx) as x with inspect (toℕ v) | inspect (toℕ idx)
path n v (π idx) as x | v' with-≡ eq | idx' with-≡ eq' with compare v' idx' 
path v _ (π idx) as x | v' with-≡ eq | .(suc (v' + k)) with-≡ eq' | less .v' k = π {!idx (with complicated crap)!}
path v _ (π idx) as x | .idx' with-≡ eq | idx' with-≡ eq' | equal .idx'  = K ⊤
path v _ (π idx) as x | .(suc (idx' + k)) with-≡ eq | idx' with-≡ eq' | greater .idx' k = K ⊥


path : {a : Set} -> (f : Funct 1) -> (x : [[ f ]] a) -> Set
path (μ arg) (In y) = {!!}
path (K t) x = ⊥
path (l ⊕ r) (inj₁ x) = path l x
path (l ⊕ r) (inj₂ y) = path r y
path (l ⊗ r) (x , y) = path l x ⊎ path r y
path (π zero) x = ⊤
path (π (suc ())) x
-}

-- postulate genLookup : (n : ℕ) (v : Fin n) (f : Funct n) (as : Vec₁ Set n) -> (x : f $! as) -> (path n v f as x -> lookup v as )

FList : Funct 1
FList = μ (K ⊤ ⊕ (π (suc zero) ⊗ π (zero)))

args : Vec₁ Set 1
args = ℕ ∷ []

test1 = FList $! args

-- test2 = path _ (zero) FList args (In (inj₂ (3 , (In (inj₂ (5 , In (inj₁ tt)))))))


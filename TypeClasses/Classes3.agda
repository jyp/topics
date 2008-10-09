open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.Unit
open import Data.List
open import Data.Empty
module Classes3 where

  -- test if two boolean values are equal
  boolTest : Bool -> Bool -> Bool 
  boolTest true true = true
  boolTest false false = true
  boolTest _ _ = false


  -- we work on a closed universe of types, whose codes are as follows:
  data Code : Set where
    boolCode : Code
    natCode  : Code
    listCode : Code -> Code

  ⟦_⟧ : Code -> Set
  ⟦ boolCode ⟧ = Bool
  ⟦ natCode ⟧  = ℕ
  ⟦ listCode c ⟧ = [ ⟦ c ⟧ ]


  data _≡_ {a : Set1} (x : a) : a -> Set1 where
    ≡-refl : x ≡ x

  test : (x : Set) -> x ≡ ⊥ 
  test = {! !}

  data Dec : Set2 where
    top : (x : Set) -> x ≡ ⊤ ->  Dec
    bot : (x : Set) -> x ≡ ⊥ -> Dec

  IsJust' : {a : Set} -> Maybe a -> Dec 
  IsJust' (just _) = top ⊤  ≡-refl
  IsJust' nothing  = bot ⊥ ≡-refl


  IsJust : {a : Set} -> Maybe a -> Set
  IsJust (just _) = ⊤
  IsJust nothing  = ⊥



  -- a class
  record Class : Set1 where
    field
     sig : Set -> Set                            -- mapping parameters to specific signature
       -- superclasses could be expressed as elements of the signature
     instances : (c : Code) -> Maybe (sig ⟦ c ⟧) -- mapping codes to definitions

  -- Constraint on a given class 
  Constraint : Class -> Code -> Dec
  Constraint class c = IsJust' (Class.instances class c)


-----------------------------
-- Example: "Equality" class


  -- Signature for Eq class
  record EqClassSig (t : Set) : Set where
    field 
      == : t -> t -> Bool

  mapMaybe : {a : Set} -> {b : Set} -> (a -> b) -> Maybe a -> Maybe b
  mapMaybe f nothing = nothing
  mapMaybe f (just x) = just (f x)   

  zipWith : forall {a b c} -> (a -> b -> c) -> [ a ] -> [ b ] -> [ c ]
  zipWith f [] _ = []
  zipWith f _ [] = []
  zipWith f (a ∷ as) (b ∷ bs) = f a b ∷ zipWith f as bs

  -- Instances for the Eq class
  eqClassInstances : (c : Code) -> Maybe (EqClassSig ⟦ c ⟧)
  eqClassInstances boolCode = just (record {== = boolTest})
  eqClassInstances _        = nothing
  eqClassInstances (listCode c) = mapMaybe 
      (\argDict -> record {== = \l1 l2 -> and (zipWith (EqClassSig.== argDict) l1 l2) })
      (eqClassInstances c)
      -- polymorphic instance

  -- Definition of the Eq class
  eqClass : Class
  eqClass = record {sig = EqClassSig; instances = eqClassInstances}

  -- matching on having a type-class or not (see "beautiful" example)
  eq2 : {c : Code} -> ⟦ c ⟧ -> ⟦ c ⟧ -> ⟦ c ⟧ -> Bool
  eq2 {c} x y z with Class.instances eqClass c
  ...         | just sig = let _==_ = EqClassSig.== sig in (x == y) ∧ (y == z)
  ...         | nothing = false


  -- The "Eq" constraint
  Eq : Code -> Dec
  Eq = Constraint eqClass

  -- enforcing class constraints / convenient access:
  _≠_ : {c : Code} -> Eq c -> ⟦ c ⟧ -> ⟦ c ⟧ -> Bool
  _≠_ {c} {p}  x y = ?
--   _≠_ {c} {p}  x y with Class.instances eqClass c
--   _≠_ {c} {_}  x y  | just sig = not (EqClassSig.== sig x y)
--   _≠_ {c} {_} x y  | nothing = ?

  -- using at a monomorphic type
  neqBools : Bool -> Bool -> Bool
  neqBools = _≠_
    


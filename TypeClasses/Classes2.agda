open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.Unit
open import Data.List
open import Data.Empty

module Classes2 where

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
  Constraint : Class -> Code -> Set
  Constraint class c = IsJust (Class.instances class c)


-----------------------------
-- Example: "Equality" class


  -- Signature for Eq class
  record EqClassSig (t : Set) : Set where
    field 
      equality : t -> t -> Bool

  mapMaybe : {a : Set} -> {b : Set} -> (a -> b) -> Maybe a -> Maybe b
  mapMaybe f nothing = nothing
  mapMaybe f (just x) = just (f x)   

  zipWith : forall {a b c} -> (a -> b -> c) -> [ a ] -> [ b ] -> [ c ]
  zipWith f [] _ = []
  zipWith f _ [] = []
  zipWith f (a ∷ as) (b ∷ bs) = f a b ∷ zipWith f as bs

  -- Instances for the Eq class
  eqClassInstances : (c : Code) -> Maybe (EqClassSig ⟦ c ⟧)
  eqClassInstances boolCode = just (record {equality = boolTest})
  eqClassInstances _        = nothing
  eqClassInstances (listCode c) = mapMaybe 
      (\argDict -> record {equality = \l1 l2 -> and (zipWith (EqClassSig.equality argDict) l1 l2) })
      (eqClassInstances c)
      -- polymorphic instance

  -- Definition of the Eq class
  eqClass : Class
  eqClass = record {sig = EqClassSig; instances = eqClassInstances}

  -- matching on having a type-class or not (see "beautiful" example)
  eq2 : {c : Code} -> ⟦ c ⟧ -> ⟦ c ⟧ -> ⟦ c ⟧ -> Bool
  eq2 {c} x y z with Class.instances eqClass c
  ...         | just sig = let _==_ = EqClassSig.equality sig in (x == y) ∧ (y == z)
  ...         | nothing = false


  -- The "Eq" constraint
  Eq : Code -> Set
  Eq = Constraint eqClass



  -- enforcing class constraints / convenient access:
  _==_ : {c : Code} -> {p : Eq c} -> ⟦ c ⟧ -> ⟦ c ⟧ -> Bool
  _==_ {c} {p}  with Class.instances eqClass c
  _==_ {c} {_}   | just sig = EqClassSig.equality sig 
  _==_ {c} {()}  | nothing

  -- generalizing...
  use : {res : Set} -> {cl : Class} -> {c : Code} -> (fld : (Class.sig cl ⟦ c ⟧ -> res)) -> {p : Constraint cl c} -> res
  use {res} {cl} {c} fld {p}   with Class.instances cl c
  use {res} {cl} {c} fld {p}     | just sig = fld sig
  use {res} {cl} {c} fld {()}    | nothing

  _===_ : {c : Code} -> {p : Eq c} -> ⟦ c ⟧ -> ⟦ c ⟧ -> Bool
  _===_ {p = p} = use {cl = eqClass} EqClassSig.equality {p = p} 

  -- propagation of constraints
  _≠_ : {c : Code} -> {p : Eq c} -> ⟦ c ⟧ -> ⟦ c ⟧ -> Bool
  _≠_ {p = p} x y = _==_ {p = p} x y 

  -- using at a monomorphic type
  neqBools : Bool -> Bool -> Bool
  neqBools = _≠_
    
  -- propagation of constraints
  test : {c : Code} -> {p : Eq c} -> ⟦ c ⟧ -> ⟦ c ⟧ -> ⟦ c ⟧ -> Bool
  test {p = p} x y z = (_≠_ {p = p} x y) ∨ (_≠_ {p = p} y z)
  -- we have to specify constraints explicitly: no solver in Agda.

  -- misusing at a monomorphic type
  neqNats : {p : Eq natCode} -> ℕ -> ℕ -> Bool
  neqNats {p} = _≠_ {p = p} 
  -- Note: we can define a "wrong" function, and leave the burden of proof to the caller.
  -- (I think this is akin to so called "axiomatic classes" in Isabelle.)

  -- In other words, it's possible to leave the constraint "floating"
  -- (not discharge it) even when instanciated at precise types.


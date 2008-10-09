open import Data.Nat
open import Data.Bool

module Classes2 where

  data Maybe (a : Set1) : Set1 where
    just    : a -> Maybe a
    nothing : Maybe a


  -- test if two boolean values are equal
  boolTest : Bool -> Bool -> Bool 
  boolTest true true = true
  boolTest false false = true
  boolTest _ _ = false


  -- we work on a closed universe of types, whose codes are as follows:
  data Code : Set where
    boolCode : Code
    natCode  : Code
--    listCode : Code -> Code

  ⟦_⟧ : Code -> Set
  ⟦ boolCode ⟧ = Bool
  ⟦ natCode ⟧  = ℕ

  -- a class
  record Class : Set2 where
    field
     sig : Set -> Set1                            -- mapping parameters to specific signature
     instances : (c : Code) -> Maybe (sig ⟦ c ⟧) -- mapping codes to definitions

  -- Helper type to enforce that a value is "just" (in Maybe)
  data IsJust {a : Set1} : Maybe a -> Set1 where
    isJust : {x : a} -> IsJust (just x)

  -- Constraint on a given class 
  Constraint : Class -> Code -> Set1
  Constraint class c = IsJust (Class.instances class c)


-----------------------------
-- Example: "Equality" class


  -- Signature for Eq class
  record EqClassSig (t : Set) : Set1 where
     field
       Comparison : Set
       == : t -> t -> Comparison
       
   
  -- Instances for the Eq class
  eqClassInstances : (c : Code) -> Maybe (EqClassSig ⟦ c ⟧)
  eqClassInstances boolCode = just (record {== = boolTest; Comparison = Bool})
  eqClassInstances _        = nothing
  
  -- Definition of the Eq class
  eqClass : Class
  eqClass = record {sig = EqClassSig; instances = eqClassInstances}

  -- The "Eq" constraint
  Eq : Code -> Set1
  Eq = Constraint eqClass

  -- convenient access to the type
  compTyp : (c : Code) -> (p : Eq c) -> Set
  compTyp c p      with Class.instances eqClass c
  compTyp c ()         | nothing
  compTyp c isJust     | just sig = EqClassSig.Comparison sig

  -- convenient access to the function
  eq2' : {c : Code} -> {p : Eq c} -> ⟦ c ⟧ -> ⟦ c ⟧ -> compTyp c p
  eq2' {c} {p}      x y with Class.instances eqClass c
  eq2' {c} {IsJust} x y | just sig = let _==_ = EqClassSig.== sig in {!_==_ !} -- err?
  eq2' {c} {()}     x y | nothing


  -- using at a monomorphic type
  eqBools : Bool -> Bool -> Bool
  eqBools = eq2' {boolCode} {isJust} -- strange that these can't be inferred!



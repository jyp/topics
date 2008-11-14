open import Data.Nat
open import Data.Fin
open import Data.Bool
open import Data.Maybe
open import Data.Vec

module MPTC where

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

  data Vec₁ (a : Set1) : ℕ -> Set1 where
    []₁  : Vec₁ a zero
    _∷₁_ : forall {n} -> a -> Vec₁ a n -> Vec₁ a (suc n)

  lookup₁ : forall {a n} -> Fin n -> Vec₁ a n -> a
  lookup₁ zero     (x ∷₁ xs) = x
  lookup₁ (suc i) (x ∷₁ xs) = lookup₁ i xs


  map₀₁ : forall {a b n} -> (a -> b) -> Vec a n -> Vec₁ b n
  map₀₁ f [] = []₁
  map₀₁ f (x ∷ xs) = f x ∷₁ map₀₁ f xs

  ⟦_⟧ⁿ : forall {n} -> Vec Code n -> Vec₁ Set n
  ⟦_⟧ⁿ = map₀₁ ⟦_⟧


  -- a class
  record Class : Set1 where
    field
     arity : ℕ
     sig : Vec₁ Set arity -> Set                  -- mapping parameters to specific signature
     instances : (c : Vec Code arity) -> Maybe (sig ⟦ c ⟧ⁿ) -- mapping codes to definitions

  -- Helper type to enforce that a value is "just" (in Maybe)
  data IsJust {a : Set} : Maybe a -> Set where
    isJust : {x : a} -> IsJust (just x)

  -- Constraint on a given class 
  Constraint : (class : Class) -> Vec Code (Class.arity class) -> Set
  Constraint class c = IsJust (Class.instances class c)


-----------------------------
-- Example: "Equality" class


  -- Signature for Eq class
  record EqClassSig (t : Vec₁ Set 2) : Set where
     field 
       == : lookup₁ zero t -> lookup₁ (suc zero) t -> Bool
   
  -- Instances for the Eq class
  eqClassInstances : (c : Vec Code 2) -> Maybe (EqClassSig ⟦ c ⟧ⁿ)
  eqClassInstances (boolCode ∷ boolCode ∷ []) = just (record {== = boolTest})
  eqClassInstances _        = nothing
  
  -- Definition of the Eq class
  eqClass : Class
  eqClass = record {arity = 2; sig = EqClassSig; instances = eqClassInstances}

  -- matching on having a type-class or not (see "beautiful" example)
  eq2 : {c : Code} -> ⟦ c ⟧ -> ⟦ c ⟧ -> ⟦ c ⟧ -> Bool
  eq2 {c} x y z with Class.instances eqClass (c ∷ c ∷ [])
  ...         | just sig = let _==_ = EqClassSig.== sig in (x == y) ∧ (y == z)
  ...         | nothing = false


  -- The "Eq" constraint
  Eq : Code -> Code -> Set
  Eq c d = Constraint eqClass (c ∷ d ∷ [])

  -- enforcing class constraints:
  eq2' : {c : Code} -> {p : Eq c c} -> ⟦ c ⟧ -> ⟦ c ⟧ -> ⟦ c ⟧ -> Bool
  eq2' {c} {p} x y z with Class.instances eqClass (c ∷ c ∷ [])
  eq2' {c} {IsJust} x y z | just sig = let _==_ = EqClassSig.== sig in (x == y) ∧ (y == z)
  eq2' {c} {()} x y z     | nothing


  -- using at a monomorphic type
  eqBools : Bool -> Bool -> Bool -> Bool
  eqBools = eq2' {boolCode} {isJust} -- strange that these can't be inferred!


  -- misusing at a monomorphic type
  eqNats : ℕ -> ℕ -> ℕ -> Bool
  eqNats = eq2' {natCode} {{! !}} 
  -- Note: we can define a "wrong" function, and leave the burden of proof to the caller.
  -- (I think this is akin to so called "axiomatic classes" in Isabelle.)


  ----------------------------------------------------------------
  -- Signature for zero-parameter class
  record ZeroClassSig (t : Vec₁ Set 0) : Set where
     field 
       hello : ℕ
  -- Instances for the Zero class
  zeroClassInstances : ℕ -> (c : Vec Code 0) -> Maybe (ZeroClassSig ⟦ c ⟧ⁿ)
  zeroClassInstances n _ = just (record { hello = n })

  -- Definition of the Zero class
  zero5Class : Class
  zero5Class = record {arity = 0; sig = ZeroClassSig; instances = zeroClassInstances 5}

  -- The zero-parameter concepts are basically records.

open import Data.Nat    using (ℕ)
open import Data.Bool   using (Bool; true; false; _∧_)
open import Data.Maybe  using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Classes2 where

  -- test if two boolean values are equal
  boolTest : Bool -> Bool -> Bool 
  boolTest true  true  = true
  boolTest false false = true
  boolTest _     _     = false


  data Code : Set where
    boolCode : Code
    natCode  : Code
--    listCode : Code -> Code

  ⟦_⟧ : Code -> Set
  ⟦ boolCode ⟧ = Bool
  ⟦ natCode ⟧  = ℕ


  -- postulate Vec : ℕ -> Set -> Set

--   Class = { n : ℕ } ->                 -- Arity of the class
--           (Sig : Vec n Set -> Set) ->    -- Signature of the class
--           (tc : Vec n Code) ->           -- typecodes
--           Maybe (Sig (map universe tc))  -- Maybe a signature for the given set of tc.


  -- A class of a given signature is a function from typecodes to dictionaries (maybe...)
  -- (if we ignore signatures it is a relation between typecodes)
  Class : (Sig : Set -> Set) -> Set    -- Signature of the class
  Class Sig = (c : Code) ->            -- typecodes
              Maybe (Sig ⟦ c ⟧)        -- Maybe a signature for the given set of tc.

  -- Constraint on a given class 
  record Constraint {sig : Set -> Set} (class : Class sig) (c : Code) : Set where
    field
      dictionary : sig ⟦ c ⟧ 
      -- dictionary for the class (a value of the correct signature)
      p : class c ≡ just dictionary
      -- proof that the above value is actually the one from the class
      -- Incidentally, this also proves that there is an instance for that type



-----------------------------
-- Example: "Equality" class


  -- Signature for Eq class
  record EqClassSig (t : Set) : Set where
     field 
       == : t -> t -> Bool

  
  -- Definition of the Eq class
  eqClass : Class EqClassSig

  -- And instances
  eqClass boolCode = just (record {== = boolTest})
  eqClass _        = nothing


  -- The "Eq" constraint
  Eq : Code -> Set
  Eq = Constraint {EqClassSig} eqClass   -- ugly that EqClassSig has to be specified 


  -- adding TC. constraints
  eq2' : {c : Code} -> {dict : Eq c} 
         -> ⟦ c ⟧ -> ⟦ c ⟧ -> ⟦ c ⟧ -> Bool
  eq2' {_} {dict} x y z = let _==_ = EqClassSig.== (Constraint.dictionary dict)
                          in (x == y) ∧ (y == z)


  -- matching on having a type-class or not (see "beautiful" example)
  eq2 : {c : Code} -> ⟦ c ⟧ -> ⟦ c ⟧ -> ⟦ c ⟧ -> Bool
  eq2 {c} x y z with eqClass c
  ...         | just sig = let _==_ = EqClassSig.== sig in (x == y) ∧ (y == z)
  ...         | nothing = false

  
  -- using a constrained function on a particular type
  useEq2 : ℕ -> ℕ -> ℕ -> Bool
  useEq2 x y z = eq2' {natCode} {record {dictionary = {! !} ; p = {! !}}} x y z

  
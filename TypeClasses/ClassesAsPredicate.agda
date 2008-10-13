module ClassesAsPredicate where

  open import Data.Nat
  open import Data.Bool
  open import Data.Unit
  open import Data.List
  open import Data.Empty
  open import Relation.Binary.PropositionalEquality


  data Maybe1 (a : Set1) : Set1 where
    just    : a -> Maybe1 a
    nothing : Maybe1 a


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
  ⟦ listCode c ⟧ = List ⟦ c ⟧

  IsJust : {a : Set1} -> Maybe1 a -> Set
  IsJust (just _) = ⊤
  IsJust nothing  = ⊥


  -- encoding a type class
  record Class : Set2 where
    field
     sig : Set -> Set1
     -- Mapping (type) parameter to specific signature

     -- This returns a "Set1" so that the result can contain associated types,

     instances : (c : Code) -> Maybe1 (sig ⟦ c ⟧) -- mapping codes to definitions
      -- we need to use a code so that the "instances" function can pattern-match on something.


  -- Constraint on a given class 
  Constraint : Class -> Code -> Set
  Constraint class c = IsJust (Class.instances class c)

  -- generalizing: one can use a "method" given the constraint.
  use : {res : Set} -> {cl : Class} -> {c : Code} -> (method : (Class.sig cl ⟦ c ⟧ -> res)) -> {p : Constraint cl c} -> res
  use {res} {cl} {c} method {p}   with Class.instances cl c
  use {res} {cl} {c} method {p}     | just sig = method sig
  use {res} {cl} {c} method {()}    | nothing


  module EqualityExample where
  
    -- Signature for Eq class
    record EqClassSig (t : Set) : Set1 where
      field 
        equality : t -> t -> Bool

    mapMaybe : forall {a b} -> (a -> b) -> Maybe1 a -> Maybe1 b
    mapMaybe f nothing = nothing
    mapMaybe f (just x) = just (f x)   

    zipWith : forall {a b c} -> (a -> b -> c) -> List a -> List b -> List c
    zipWith f [] _ = []
    zipWith f _ [] = []
    zipWith f (a ∷ as) (b ∷ bs) = f a b ∷ zipWith f as bs

    -- Instances for the Eq class
    eqClassInstances : (c : Code) -> Maybe1 (EqClassSig ⟦ c ⟧)
    eqClassInstances boolCode = just (record {equality = boolTest})
    eqClassInstances natCode  = nothing
    eqClassInstances (listCode c) = mapMaybe 
        (\argDict -> record {equality = \l1 l2 -> and (zipWith (EqClassSig.equality argDict) l1 l2) })
        (eqClassInstances c)
        -- example: modelling a polymorphic instance

    -- Definition of the Eq class
    eqClass : Class
    eqClass = record {sig = EqClassSig; instances = eqClassInstances}

    -- "concept-based overloading"
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


    -- Alternate definition using the generic "use" function
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

  

    -- simplifying constraints:
    -- We can construct a "more complex" constraint if it's implied by a
    -- simpler one, as such:
    simplify : (c : Code) -> Eq c -> Eq (listCode c)
    simplify c cons with eqClassInstances c 
    simplify c cons | just x = tt
    simplify c ()   | nothing

  module OrdExample where

    import Relation.Binary using (Rel)

    record OrdClassSig (t : Set) : Set1 where
      field 
        _[<=]_ : t -> t -> Bool
        [>=-trans] : {a b c : t} -> T (a [<=] b) -> T (b [<=] c) -> T (a [<=] c)
        [superEq] : {c : Code} {- -> [[c]] == t -} -> EqualityExample.Eq c
        
      
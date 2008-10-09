open import Data.Nat
open import Data.Bool
open import Data.Maybe

module Classes where

-- postulate Vec : ℕ -> Set -> Set

--   Class = { n : ℕ } ->                 -- Arity of the class
--           (Sig : Vec n Set -> Set) ->  -- Signature of the class

--           (types : Vec n Set) ->       -- types
--           Maybe (Sig types)            -- Maybe a signature for given types

  Class : Set1
  Class = (Sig : Set -> Set) ->    -- Signature of the class
          (types : Set) ->         -- types
          Maybe (Sig types)        -- Maybe a signature for the given set of types.

--  EqClassSig : Set -> Set
--  EqClassSig t = (t -> t -> Bool) -- should be a record, etc.

  data EqClassSig (t : Set) : Set where
     eqClassSig : (t -> t -> Bool) -> EqClassSig t


  
--  eqClass : Class EqClassSig
  eqClass : (t : Set) -> Maybe (EqClassSig t)
  eqclass Bool     = ?
  eqClass _        = nothing


--   eq2 : {t : Set} -> t -> t -> t -> Bool
--   eq2 {t} a b c with eqClass t
--   ...         |  just (==) = (a == b) ∧ (b == c)
--   ...         |  nothing = false
 
--  HasClass c t = isJust (c t)

--   eq2' : {t : Set} -> {HasClass eqClass t} -> t -> t -> t -> Bool



  
{- OPTIONS --type-in-type #-}
module Param where

  open import Data.Nat
  open import Data.Bool
  
  Nat : Set
  Nat = ℕ

--   data Bool : Set where
--     true : Bool
--     false : Bool
-- 
--   if_then_else : forall {a : Set} -> Bool -> a -> a -> a
--   if true  then x else _ = x
--   if false then _ else x = x
-- 
--   data Nat : Set where
--     zero : Nat
--     suc  : Nat -> Nat
-- 
--   _==_ : Nat -> Nat -> Bool
--   zero == zero = true
--   zero == _ = false
--   _ == zero = false
--   suc x == suc y = x == y

  data TC : Set1 where 
     con : Set -> TC
     var : Nat -> TC
     fun : TC -> TC -> TC
     abs : Nat -> TC -> TC
  

  typeOf : (Nat -> Set) -> TC -> Set -- todo: compute the kind.
  typeOf _ (con y) = y
  typeOf env (var x) = env x
  typeOf env (fun y y') = typeOf env y -> typeOf env y'
  typeOf env (abs w y) = forall {a : Set} -> typeOf (env' a) y 
    where env' : Set -> (Nat -> Set)
          env' a v = if v == w then a else (env v)

  data _===_ {A : Set} (a : A) : (A -> Set) where
    refl : a === a

  paramTest : (f : ((a : Set) -> a -> a)) -> (b : Set) -> (x : b) -> f b x === x 
  paramTest f b x = {!!}
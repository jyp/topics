{-# OPTIONS --type-in-type #-}
module Param where

  open import Data.Empty
  open import Data.Nat
  -- open import Data.Bool
  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary.Core using (Rel)
  open import Relation.Nullary

  Nat : Set
  Nat = ℕ

  if_then_else_ : forall {p} -> {a : Set1} -> Dec p -> a -> a -> a
  if yes p then t else f = t
  if no p then t else f = f

  data TC : Set1 where 
     con : Set -> TC
     var : Nat -> TC
     fun : TC -> TC -> TC
     abs : Nat -> TC -> TC

  
  Env : Set1 -> Set1
  Env a = Nat -> a

  emptyEnv : forall {a} -> a -> Env a
  emptyEnv c _ = c

  addEnv : forall {a} -> Nat -> a -> Env a -> Env a
  addEnv w a env v = (if v ≟ w then a else env v)  


  typeOf : (Env Set) -> TC -> Set -- todo: compute the kind.
  typeOf _ (con y) = y
  typeOf env (var x) = env x
  typeOf env (fun y y') = typeOf env y -> typeOf env y'
  typeOf env (abs w y) = {a : Set} -> typeOf (addEnv w a env) y 
  
  typeOfClosed = typeOf (emptyEnv ⊥)

  param : (tc : TC) -> Rel (typeOfClosed tc)
  param (con y) = _≡_
  param (var y) = {!!}
  param (fun y y') = \f f' -> {!!} -- ∀ x x'. param y x x' ⇒ param y' (f x) (f' x') 
  param (abs y y') = {!!}

  paramTest : (f : ({a : Set} -> a -> a)) -> (b : Set) -> (x : b) -> f x ≡ x 
  paramTest f b x = {!!}


  


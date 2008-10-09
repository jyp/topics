{-# OPTIONS --no-positivity-check
  #-}

module Open2 where
open import Data.Unit
-- open import Logic
import Data.Nat as Nat
open import Data.Function
open Nat using (ℕ)
open Nat using (suc; zero)
open Nat renaming ( _+_ to _+n_)
open import Data.Bool

data _×_ (a : Set) (b : Set) : Set where
  _,_ : a -> b -> a × b 

infixr 6 _×_
infixr 6 _,_

data _×₁_ (a : Set1) (b : Set1) : Set1 where
  _,₁_ : a -> b -> a ×₁ b 

outr : forall {a b} -> a × b -> b
outr ( x , y ) = y

outl : forall {a b} -> a × b -> a
outl ( x , y ) = x

data _+_ (a : Set) (b : Set) : Set where
  inl : a -> a + b
  inr : b -> a + b

[_,_] :  {a b c : Set}
      -> (a -> c) -> (b -> c) -> (a + b -> c)
[ f , g ] (inl x) = f x
[ f , g ] (inr y) = g y

⟨_,_⟩ :  {a b c : Set}
      -> (a -> b) -> (a -> c) -> (a -> b × c)
⟨ f , g ⟩ x = ( f x , g x )


_×f_ : {a b c d : Set} -> (a -> b) -> (c -> d) -> (a × c -> b × d)
f ×f g = ⟨ f ∘ outl , g ∘ outr ⟩
infixr 6 _×f_

record Functor : Set1 where
  field
    F : Set -> Set
    f : {A B : Set} -> (A -> B) -> F A -> F B

o : Functor -> Set -> Set
o = Functor.F

Alg : Functor -> {A : Set} -> Set
Alg F {A} = o F A -> A


map : (F : Functor) {A : Set} {B : Set} -> (A -> B) -> o F A -> o F B
map = Functor.f


data T {F : Functor} : Set where
    α : o F (T {F}) -> T

α⁻¹ : {F : Functor} -> T {F} -> o F T
α⁻¹ (α x) = x

cata : {F : Functor} -> {A : Set} -> Alg F -> (T {F} -> A)
cata {F} h = h ∘ map F (cata h) ∘ α⁻¹

irr : {F : Functor} -> {A : Set} -> (T {F} × o F A -> A) -> (T {F} -> A)
irr {F} h = h ∘ (id ×f map F (irr h)) ∘ ⟨ id , α⁻¹ ⟩

natF : Functor
natF = record {
              F = \A -> ⊤ + A;
              f = \h -> [ inl , inr ∘ h ]
        }

unitF : Functor
unitF = record {
  F = \B -> ⊤;
  f = \h -> \x -> x
 }

rec1F : Set -> Functor
rec1F A = record {
  F = \B -> A × B;
  f = \h -> id ×f h
 }

listF : Set -> Functor
listF A = record {
     F = \B -> ⊤ + (A × B);
     f = \h -> [ inl , inr ∘ (id ×f h) ]
   }

treeF : Set -> Functor
treeF A = record {
     F = \B -> ⊤ + (B × A × B);
     f = \h -> [ inl , inr ∘ (h ×f id ×f h) ]
   }

rec2F : Set -> Functor
rec2F A = record {
  F = \B -> B × A × B;
  f = \h -> h ×f id ×f h
 }


boolF : Functor
boolF = record {
    F = \B -> ⊤ + ⊤;
    f = \h -> [ inl , inr ]
 }


_+F_ : Functor -> Functor -> Functor
a +F b = record {
                 F = \T -> Functor.F a T + Functor.F b T;
                 f = \h -> [ inl ∘ Functor.f a h , inr ∘ Functor.f b h ]
               }
infixr 6 _+F_

_+A_ : {A : Set} {F G : Functor} -> Alg F -> Alg G -> Alg (F +F G) {A}
f +A g = [ f , g ]


max : ℕ -> ℕ -> ℕ
max zero x = x 
max x zero = x
max (suc x) (suc y) = suc (max x y)

depthU : Alg unitF
depthU = const 0

depthT : {A : Set} -> Alg (rec2F A)
depthT ( l , x , r ) = suc (max l r)

depthL : {A : Set} -> Alg (rec1F A)
depthL ( x , rec ) = suc rec

mixF : Set -> Functor
mixF A = unitF +F rec1F A +F rec2F A

mixDepth : {A : Set} -> T {mixF A} -> ℕ
mixDepth = cata [ depthU , [ depthL , depthT ] ]

addCase : {F : Functor } -> {A : Set} -> (o F A -> Bool) -> Alg F {A} -> Alg F {A} -> Alg F
addCase pred algT algF input with pred input
...                      | False = algT input
...                      | True = algF input



{-# OPTIONS --no-positivity-check
  #-}

module Open where
open import Data.Unit
open import Logic
import Data.Nat as Nat
open import Data.Function
open Nat using (ℕ)
open Nat using (suc; zero)
open Nat renaming ( _+_ to _+n_)


data _×_ (a : Set) (b : Set) : Set where
  _,_ : a -> b -> a × b 

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

record Functor : Set1 where
  field
    F : Set -> Set
    f : {A B : Set} -> (A -> B) -> F A -> F B



record TermAlgebra : Set1 where
  field BaseFunctor : Functor
  open Functor BaseFunctor

  data T : Set where
    α : F T -> T

  α⁻¹ : T -> F T
  α⁻¹ (α x) = x

  cata : {A : Set} -> (F A -> A) -> (T -> A)
  cata h = h ∘ f (cata h) ∘ α⁻¹


nat : TermAlgebra
nat = record {
        BaseFunctor = record {
          F = \A -> ⊤ + A;
          f = \h -> [ inl , inr ∘ h ]
        }
    }


list : Set -> TermAlgebra
list A = record {
  BaseFunctor = record {
    F = \B -> ⊤ + (A × B);
    f = \h -> [ inl , inr ∘ id ×f h ]
  }
 }

bool : TermAlgebra
bool = record {
  BaseFunctor = record {
    F = \B -> ⊤ + ⊤;
    f = \h -> [ inl , inr ]
  }
 }


boolAlgebra : TermAlgebra
boolAlgebra = record {
  BaseFunctor = record {
    F = \B -> ⊤ + ⊤;
    f = \h -> [ inl , inr ]
  }
 }

record BoolAlgebra : Set1 where
  open TermAlgebra boolAlgebra
  open Functor BaseFunctor

  true0 : _ -> _ + _
  true0 = inl

  false0 : _ -> _ + _
  false0 = inr
 
  true : ⊤ -> T
  true = α ∘ inl

  false : ⊤ -> T
  false = α ∘ inr

  not : T -> T
  not = cata [ false , true ]

  not0 : _ + _ -> _ + _
  not0 = [ false0 , true0 ]

  not1 : ⊤ + ⊤ -> T
  not1 = α ∘ [ false0 , true0 ]

unitAlgebra : TermAlgebra
unitAlgebra = record {
  BaseFunctor = record {
    F = \B -> ⊤;
    f = \h -> id
  }
 }

module UnitAlgebra where
  open TermAlgebra unitAlgebra

  unit : ⊤ -> T
  unit = α ∘ id

  not : T -> T
  not = cata unit


_+Functor_ : Functor -> Functor -> Functor
a +Functor b = record {
                 F = \T -> Functor.F a T + Functor.F b T;
                 f = \h -> [ inl ∘ Functor.f a h , inr ∘ Functor.f b h ]
               }


_+Algebra_ : TermAlgebra -> TermAlgebra -> TermAlgebra
a +Algebra b = record { BaseFunctor = TermAlgebra.BaseFunctor a +Functor TermAlgebra.BaseFunctor b }

-- 
-- record PlusAlgebra : Set1 where
--   field
--     left  : TermAlgebra
--     right : TermAlgebra
-- 
--   mix = left +Algebra right
-- 
-- 

mixAlgebra = boolAlgebra +Algebra unitAlgebra

record MixAlgebra : Set1 where
   open TermAlgebra mixAlgebra

   unit' : ⊤ -> T
   unit' = α ∘ inr ∘ TermAlgebra.α⁻¹ unitAlgebra ∘ UnitAlgebra.unit

   X =  [ [ inl , inr ] , id ]
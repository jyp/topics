{-# OPTIONS --no-positivity-check  #-}

module Fun2 where


open import Data.Unit
open import Data.Bool
open import Data.Maybe
open import Data.Empty
open import Data.String


data Type : Set1 where
     var : Type
     _==>_ : Type -> Type -> Type
     con : Set -> Type

infixr 2 _==>_

data _+0_ (A : Set) (B : Set) : Set where
  L : A -> A +0 B
  R : B -> A +0 B

data _×0_ (A : Set) (B : Set) : Set where
  _,_ : A -> B -> A ×0 B
  

data Functor : Set1 where
  id : Functor
  k1 : Set -> Functor
  _+_ : Functor -> Functor -> Functor
  _×_ : Functor -> Functor -> Functor
  z1 : Functor

infixr 1 _+_
infixr 3 _×_
  

f[_] : Functor -> Set -> Set
f[_] id s = s
f[_] (k1 y) s = y
f[_] (y + y') s = f[ y ] s +0 f[ y' ] s
f[_] (y × y') s = f[ y ] s ×0 f[ y' ] s
f[_] z1 s = ⊥

CoAlgebra : Functor -> Set1
CoAlgebra f = forall {a} -> a -> f[ f ] a

functor[[_]] : Type -> Set -> Set
functor[[ var ]] v = v
functor[[ con t ]] v = t
functor[[ _==>_ t1 t2 ]] v = functor[[ t1 ]] v → functor[[ t2 ]] v

postulate error : String -> {A : Set1} -> A

functorOf : Type -> Functor
functorOf var = id
functorOf (_==>_ y y') = error "oops."
functorOf (con y) = k1 y

[[_]] : Type -> Set1
[[ t ]] = (a : Set) -> functor[[ t ]] a



-- Bit of a functor to extract from an argument.
functorBit : Type -> Functor
functorBit var = (k1 ⊤)
functorBit (_==>_ y y') = functorOf y × functorBit y'
functorBit (con y) = z1


-- Functor of the algebra that the function depends on.
extractFunctor : Type -> Functor
extractFunctor var = z1
extractFunctor (_==>_ y y') = functorBit y + extractFunctor y'
extractFunctor (con y) = z1





data Fix (f : Set -> Set) : Set where In : f (Fix f) -> Fix f


toMonotypeArgAcc : (initialType : Set) -> (t : Type) -> (Set -> Set) -> Set
toMonotypeArgAcc i var acc = ⊤
toMonotypeArgAcc i (y ==> y') acc = toMonotypeArgAcc i y' (λ rhs → acc ((functor[[ y ]] i) → rhs))
toMonotypeArgAcc i (con y) acc = acc y

toMonotypeArg : (initialType : Set) -> (t : Type) -> Set
toMonotypeArg i t = toMonotypeArgAcc i t (λ rhs → rhs)

-- Compute the monotype for the testing 
toMonotype : (initialType : Set) -> (t : Type) -> Set
toMonotype i var = i
toMonotype i (y ==> y') = toMonotypeArg i y → toMonotype i y'
toMonotype i (con y) = y


YieldsAlgebra : Type -> Set
YieldsAlgebra var = ⊤
YieldsAlgebra (y ==> y') = YieldsAlgebra y'
YieldsAlgebra (con y) = ⊥

thm1 : ¬ YieldsAlgebra -> toMonotypeArg i y ≡ functor[[ y ]] i
thm1 = ?


algebraBit : (initialType : Set) -> (t : Type) -> (f[ functorBit t ] initialType -> initialType) -> YieldsAlgebra t -> functor[[ t ]] initialType
algebraBit i var inject ya = inject tt
algebraBit i (y ==> y') inject ya = λ fyi → algebraBit i y' (λ bit → inject ({!fyi!} , bit)) ya
algebraBit i (con y) inject ()


isZero : (f : Functor) -> Bool 
isZero id = false
isZero (k1 y) = false
isZero (y + y') = isZero y ∧ isZero y'
isZero (y × y') = isZero y ∨ isZero y'
isZero z1 = true

toMono' : (initialType : Set) -> (t : Type) -> functor[[ t ]] initialType -> toMonotype initialType t
toMono' i var v = v
toMono' i (y ==> y') v with isZero (functorOf y) 
toMono' i (y ==> y') v | true = λ arg → toMono' i y' (v {!arg!})
toMono' i (y ==> y') v | false = {!!}
toMono' i (con y) v = v

toMono : (t : Type) -> [[ t ]] -> toMonotype (Fix f[ extractFunctor t ]) t
toMono = {!!}

toTestType : Type -> Set
toTestType t = toMonotype (Fix f[ extractFunctor t ]) t


postulate AType : Set
postulate Nat : Set

binT = var ==> var ==> var
predT = var ==> con Bool
filterT = (var ==> con Bool) ==> (con Nat ==> var) ==> con Nat ==> var


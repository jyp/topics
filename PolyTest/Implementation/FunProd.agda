{-# OPTIONS --no-positivity-check  #-}

module Fun5 where


open import Data.Unit
open import Data.Nat hiding (_+_)
open import Data.Bool
open import Data.Maybe
open import Data.Empty
open import Data.String
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality1

data _+0_ (A : Set) (B : Set) : Set where
  L : A -> A +0 B
  R : B -> A +0 B

data _×0_ (A : Set) (B : Set) : Set where
  _,_ : A -> B -> A ×0 B


data Type : Set1 where
     var : Type
     _==>_ : (arg : Type) -> (res : Type) -> Type
     _××_ : (l : Type) -> (r : Type) -> Type
     con : (k : Set) -> Type

infixr 2 _==>_

NoFun : ℕ -> Type -> Set
NoFun n var = ⊤
NoFun n (con _) = ⊤
NoFun n (l ×× r) = NoFun n l ×0 NoFun n r
NoFun zero (_ ==> _) = ⊥
NoFun (suc n) (arg ==> res) = NoFun n arg ×0 NoFun (suc n) res
  

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

functor[[_]] : Type -> Set -> Set
functor[[ var ]] v = v
functor[[ con t ]] v = t
functor[[ _==>_ t1 t2 ]] v = functor[[ t1 ]] v → functor[[ t2 ]] v
functor[[ _××_ t1 t2 ]] v = functor[[ t1 ]] v ×0 functor[[ t2 ]] v

functorOf : (t : Type) -> NoFun 0 t -> Functor
functorOf var _ = id
functorOf (_==>_ y y') ()
functorOf (con y) _ = k1 y
functorOf (l ×× r) (nfl , nfr) = functorOf l nfl × functorOf r nfr

[[_]] : Type -> Set1
[[ t ]] = (a : Set) -> functor[[ t ]] a

wellBehaved : (i : Set) (t : Type) -> (nf : NoFun 0 t) -> functor[[ t ]] i ≡₁ f[ functorOf t nf ] i
wellBehaved i var _ = refl
wellBehaved i (y ==> y') ()
wellBehaved i (con y) nf = refl
wellBehaved i (l ×× r) nf = {!!}

convert : forall {a b : Set} -> (a ≡₁ b) -> a -> b
convert refl a = a

-- Bit of a functor to extract from an argument.
functorBit : (t : Type) -> NoFun 1 t -> Functor
functorBit var _ = (k1 ⊤)
functorBit  (arg ==> res) (nfa , nf) = functorOf arg nfa × functorBit res nf
functorBit (con y) _ = z1
functorBit (l ×× r) nf = {!!}


-- Functor of the algebra that the function depends on.
extractFunctor : (t : Type) -> NoFun 2 t -> Functor
extractFunctor var _  = z1
extractFunctor (_==>_ y y') (nfa , nf) = functorBit y nfa + extractFunctor y' nf
extractFunctor (con y) _ = z1
extractFunctor (l ×× r) _ = {!!}



YieldsAlgebra : Type -> Set
YieldsAlgebra var = ⊤
YieldsAlgebra (y ==> y') = YieldsAlgebra y'
YieldsAlgebra (con y) = ⊥
YieldsAlgebra (l ×× r) = {!!}

doesYieldAlgebra : (t : Type) -> Dec (YieldsAlgebra t)
doesYieldAlgebra var = yes tt
doesYieldAlgebra (y ==> y') = doesYieldAlgebra y'
doesYieldAlgebra (con y) = no (λ ())
doesYieldAlgebra (l ×× r) = {!!}


data Fix (f : Set -> Set) : Set where In : f (Fix f) -> Fix f

toMonotypeArg : (initialType : Set) -> (t : Type) -> Set
toMonotypeArg i t with doesYieldAlgebra t
... | no _ = functor[[ t ]] i
... | yes _ = ⊤

-- Compute the monotype for the testing 
toMonotype : (initialType : Set) -> (t : Type) -> Set
toMonotype i var = i
toMonotype i (y ==> y') = toMonotypeArg i y → toMonotype i y'
toMonotype i (con y) = y
toMonotype i (l ×× r) = {!!}


algebraBit : (initialType : Set) -> (t : Type) -> (nf : NoFun 1 t) -> (f[ functorBit t nf ] initialType -> initialType) -> YieldsAlgebra t -> functor[[ t ]] initialType
algebraBit i var         nf         inject ya = inject tt
algebraBit i (y ==> y')  (nfa , nf) inject ya = λ fyi → algebraBit i y' nf (λ bit → inject (convert (wellBehaved i y nfa) fyi , bit)) ya
algebraBit i (con y)     nf         inject ()
algebraBit i (l ×× r)    nf         inject ya = {!!}


toMono' : (initialType : Set) -> (t : Type) -> (nf : NoFun 2 t) -> (f[ extractFunctor t nf ] initialType -> initialType) -> functor[[ t ]] initialType -> toMonotype initialType t
toMono' i var        nf inj v = v
toMono' i (y ==> y') nf inj v with doesYieldAlgebra y
toMono' i (y ==> y') (nfa , nf) inj v | yes p = λ arg → toMono' i y' nf (λ subArg → inj (R subArg)) (v (algebraBit i y nfa (λ subArg → inj (L subArg)) p)) 
toMono' i (y ==> y') (nfa , nf) inj v | no  _ = λ arg → toMono' i y' nf (λ subArg → inj (R subArg)) (v arg)
toMono' i (con y)    nf inj v = v
toMono' i (l ×× r)   nf inj v = {!!}

toTestType : (t : Type) -> NoFun 2 t -> Set
toTestType t nf = toMonotype (Fix f[ extractFunctor t nf ]) t

toMono : (t : Type) -> (nf : NoFun 2 t) -> [[ t ]] -> toTestType t nf
toMono t nf v = toMono' initialType t nf In (v initialType) 
  where initialType = Fix f[ extractFunctor t nf ]



postulate InitialType : Set

binT = var ==> var ==> var
predT = var ==> con Bool
filterT = (var ==> con Bool) ==> (con ℕ ==> var) ==> con ℕ ==> var


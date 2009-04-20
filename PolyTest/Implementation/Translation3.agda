module Translation3 where

open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.Unit hiding (_≤_; _≤?_)
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality1

data Type : Set1 where
     var : Type
     _==>_ : (arg : Type) -> (res : Type) -> Type
     con : (k : Set) -> Type
     cross : (left : Type) -> (right : Type) -> Type

{-
work : Type -> ℕ
work var = 1
work (arg ==> res) = {!res!}
work (con k) = {!!}
work (cross left right) = {!!}
-}

[[_]] : Type -> Set -> Set
[[ var ]] v = v
[[ con t ]] v = t
[[ _==>_ t1 t2 ]] v = [[ t1 ]] v → [[ t2 ]] v
[[ cross t1 t2 ]] v = [[ t1 ]] v × [[ t2 ]] v

infixr 1 _==>_

{-
_$_ : {A : Set1} -> (a : A) -> (A -> DecP) -> Set
f $ p = DecP.prop (p f)


rank : Type -> ℕ
rank var = 1
rank (arg ==> res) = rank res  ⊔ (1 + rank arg)
rank (con k) = 0
rank (cross left right) = rank left ⊔ rank right


isConstructor : Type -> DecP
isConstructor var = True
isConstructor (arg ==> res) = isConstructor res && (rank arg <= 1)
isConstructor (con k) = False
isConstructor (cross left right) = False


isObservation : Type -> DecP
isObservation var = False
isObservation (arg ==> res) = isObservation res && (rank arg <= 1)
isObservation (con k) = True
isObservation (cross left right) = False

-}

postulate arbitrary : {A : Set} -> A
postulate fix : (Set -> Set) -> Set
postulate In : {F : Set -> Set} -> F (fix F) -> fix F

mutual


  data Args : Type -> Set1 where
    split : {s t : Type} (l : Args s) -> (r : Args t) -> Args (cross s t)
    massa : {s t : Type} -> (r : Args s) -> (p : Functor (describe s) ≡₁ Functor (describe t)) -> (out : (forall a -> [[ s ]] a -> [[ t ]] a)) -> Args t

    observ : forall {t k} -> {- rank t ≤ 1 -> -} Args (t ==> con k)
    constr : forall {t} -> {- rank t ≤ 1 -> -} Args (t ==> var)

  describe : (t : Type) -> Args t
  describe var = massa (describe (con ⊤ ==> var)) lem0 (λ a → λ f → f tt)
  describe (arg ==> var) = constr
  describe (arg ==> arg' ==> res) = massa (describe (cross arg arg' ==> res)) lem1 (λ a → λ fxy → λ x → λ y → fxy (x , y)) 
  describe (arg ==> con k) = observ
  describe (arg ==> cross left right) = massa (describe (cross (arg ==> left) (arg ==> right))) lem2 (λ a → λ fg → λ argValue → proj₁ fg argValue , proj₂ fg argValue)
  describe (con k) = massa (describe (con ⊤ ==> con k))  lem3 (λ a → λ f → f tt)
  describe (cross left right) = split (describe left) (describe right)


  Functor : forall {t} -> Args t -> (Set -> Set)
  Functor (split l r) = (λ a → Functor l a ⊎ Functor r a)
  Functor (massa r _ _) = Functor r
  Functor (observ {t}) = λ a → ⊥
  Functor (constr {t}) = [[ t ]]

  lem0 : (Functor (describe (con ⊤ ==> var)) ≡₁ Functor (describe var))
  lem0 = refl

  lem1 : forall {arg arg' res} -> (Functor (describe (cross arg arg' ==> res)) ≡₁ Functor (describe (arg ==> arg' ==> res)))
  lem1 = refl
  lem2 : forall {arg left right} -> (Functor (describe (cross (arg ==> left) (arg ==> right))) ≡₁ Functor (describe (arg ==> cross left right)))
  lem2 = refl
  lem3 : forall {k} -> (Functor (describe (con ⊤ ==> con k)) ≡₁ Functor (describe (con k)))
  lem3 = refl


-- lemma : forall (s t : Type) r {out} -> Functor {s} (massa r out) ≡₁ Functor {t} r
-- lemma s t r = refl

data Inspect1 {a : Set1} (x : a) : Set1 where
  _with-≡_ : (y : a) (eq : y ≡₁ x) → Inspect1 x

inspect1 : ∀ {a} (x : a) → Inspect1 x
inspect1 x = x with-≡ refl

convert : {F G : (Set -> Set)} (eq : F ≡₁ G) -> {a : Set} -> F a -> G a
convert refl x = x

rndArg : (μF : Set) -> (t : Type) -> (Functor (describe t) μF -> μF) -> [[ t ]] μF
rndArg μF t ι with inspect1 (describe t) 
rndArg μF .(cross s t) ι | split {s} {t} l r with-≡ eq = rndArg μF s (λ sub → ι (inj₁ sub)) , rndArg μF t (λ sub → ι (inj₂ sub))
rndArg μF .t ι | massa {s} {t} r p out with-≡ eq = out μF (rndArg μF s (λ [[Dt]]μF → ι (convert p [[Dt]]μF)))
rndArg μF .(t ==> con k) ι | observ {t} {k} with-≡ eq = λ [[t]]initialType → arbitrary
rndArg μF .(t ==> var) ι | constr {t} with-≡ eq = ι


getArg : (t : Type) -> [[ t ]] (fix (Functor (describe t)))
getArg t = rndArg (fix (Functor (describe t))) t In


{-

testArgType = cross (var ==> var ==> var) (con ℕ ==> var) 

rndArg : forall t initialType -> Args t -> [[ t ]] initialType
rndArg = {!!}

n≤k+n : forall {n k} -> n ≤ n + k
n≤k+n {zero} {k} = z≤n
n≤k+n {(suc n)} {k} = {!!}

1≤2 : 1 ≤ 2
1≤2 = n≤k+n -- s≤s z≤n

2≤2 : 2 ≤ 2
2≤2 = n≤k+n -- s≤s (s≤s z≤n)

-}
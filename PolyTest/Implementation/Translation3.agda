module Translation3 where

open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.Unit hiding (_≤_; _≤?_)
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality1




data Type : Set1 where
     var : Type
     _==>_ : (arg : Type) -> (res : Type) -> Type
     con : (k : Set) -> Type
     cross : (left : Type) -> (right : Type) -> Type

[[_]] : Type -> Set -> Set
[[ var ]] v = v
[[ con t ]] v = t
[[ _==>_ t1 t2 ]] v = [[ t1 ]] v → [[ t2 ]] v
[[ cross t1 t2 ]] v = [[ t1 ]] v × [[ t2 ]] v

infixr 1 _==>_

postulate arbitrary : (A : Set) -> A
postulate fix : (Set -> Set) -> Set
postulate In : {F : Set -> Set} -> F (fix F) -> fix F

data Args : Type -> Set1 where
  split : (s t : Type) -> Args (cross s t)
  massa : (s : Type) {t : Type} -> (out : (forall a -> [[ s ]] a -> [[ t ]] a)) -> Args t

  observ : forall {t k} -> {- rank t ≤ 1 -> -} Args (t ==> con k)
  constr : forall {t} -> {- rank t ≤ 1 -> -} Args (t ==> var)

describe : (t : Type) -> Args t
describe var = massa (con ⊤ ==> var) (λ a → λ f → f tt)
describe (arg ==> var) = constr
describe (arg ==> arg' ==> res) = massa (cross arg arg' ==> res) (λ a → λ fxy → λ x → λ y → fxy (x , y)) 
describe (arg ==> con k) = observ
describe (arg ==> cross left right) = massa (cross (arg ==> left) (arg ==> right)) (λ a → λ fg → λ argValue → proj₁ fg argValue , proj₂ fg argValue)
describe (con k) = massa (con ⊤ ==> con k)  (λ a → λ f → f tt)
describe (cross left right) = split left right


Functor : (t : Type) -> (Set -> Set)
Functor t with describe t 
Functor .(cross s t) | split s t = λ a → Functor s a ⊎ Functor t a
Functor t | massa s {.t} out = Functor s
Functor .(t ==> con k) | observ {t} {k} = λ a → ⊥
Functor .(t ==> var) | constr {t} = [[ t ]]



{-
data Inspect1 {a : Set1} (x : a) : Set1 where
  _with-≡_ : (y : a) (eq : y ≡₁ x) → Inspect1 x

inspect1 : ∀ {a} (x : a) → Inspect1 x
inspect1 x = x with-≡ refl

convert : {F G : (Set -> Set)} (eq : F ≡₁ G) -> {a : Set} -> F a -> G a
convert refl x = x
-}

rndArg : (μF : Set) -> (t : Type) -> (Functor t μF -> μF) -> [[ t ]] μF
rndArg μF t ι with describe t 
rndArg μF .(cross s t) ι | split s t = rndArg μF s (λ sub → ι (inj₁ sub)) , rndArg μF t (λ sub → ι (inj₂ sub))
rndArg μF t ι | massa s {.t} out = out μF (rndArg μF s (λ [[Dt]]μF → ι [[Dt]]μF))
rndArg μF .(t ==> con k) ι | observ {t} {k} = λ [[t]]initialType → arbitrary k
rndArg μF .(t ==> var) ι | constr {t} = ι



getArg : (t : Type) -> [[ t ]] (fix (Functor t))
getArg t = rndArg (fix (Functor t)) t In



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
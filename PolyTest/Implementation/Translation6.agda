module Translation6 where

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
open import Data.List

data Type : Set1 where
     var : Type
     _==>_ : (arg : Type) -> (res : Type) -> Type
     con : (k : Set) -> Type
     cross : (left : Type) -> (right : Type) -> Type
     list : (arg : Type) -> Type

[[_]] : Type -> Set -> Set
[[ var ]] v = v
[[ con t ]] v = t
[[ _==>_ t1 t2 ]] v = [[ t1 ]] v → [[ t2 ]] v
[[ cross t1 t2 ]] v = [[ t1 ]] v × [[ t2 ]] v
[[ list t1 ]] v = List ([[ t1 ]] v)

infixr 1 _==>_

postulate arbitrary : (A : Set) -> A
postulate fix : (Set -> Set) -> Set
postulate In : {F : Set -> Set} -> F (fix F) -> fix F

postulate replaceElements : forall {a} -> List ⊤ -> (ℕ -> a) -> List a

data Args : Type -> Set1 where
  split : (s t : Type) -> Args (cross s t)
  massag : (s : Type) {t : Type} -> (out : (forall a -> [[ s ]] a -> [[ t ]] a)) -> Args t

  observ : forall {t k} -> {- rank t ≤ 1 -> -} Args (t ==> con k)
  constr : forall {t} -> {- rank t ≤ 1 -> -} Args (t ==> var)


describe : (t : Type) -> Args t
describe (x ==> list arg) = massag (cross (x ==> con (List ⊤)) (con ℕ ==> arg)) (λ a → λ struc,rec → λ theX → replaceElements (proj₁ struc,rec theX) (proj₂ struc,rec))
describe (arg ==> var) = constr
describe (arg ==> arg' ==> res) = massag (cross arg arg' ==> res) (λ a → λ fxy → λ x → λ y → fxy (x , y)) 
describe (arg ==> con k) = observ
describe (arg ==> cross left right) = massag (cross (arg ==> left) (arg ==> right)) (λ a → λ fg → λ argValue → proj₁ fg argValue , proj₂ fg argValue)
describe (cross left right) = split left right
-- add a dummy argument.
describe (con k) = massag (con ⊤ ==> con k)  (λ a → λ f → f tt)
describe var = massag (con ⊤ ==> var) (λ a → λ f → f tt)
describe (list arg) = massag (con ⊤ ==> list arg)  (λ a → λ f → f tt)


Functor : (t : Type) -> (Set -> Set)
Functor t with describe t 
Functor .(cross s t)   | split s t = λ a → Functor s a ⊎ Functor t a
Functor t              | massag s {.t} out = Functor s
Functor .(t ==> con k) | observ {t} {k} = λ a → ⊥
Functor .(t ==> var)   | constr {t} = [[ t ]]

rndArg : (μF : Set) -> (t : Type) -> (Functor t μF -> μF) -> [[ t ]] μF
rndArg μF t ι with describe t 
rndArg μF .(cross s t) ι | split s t = rndArg μF s (λ sub → ι (inj₁ sub)) , rndArg μF t (λ sub → ι (inj₂ sub))
rndArg μF t ι | massag s {.t} out = out μF (rndArg μF s ι)
rndArg μF .(t ==> con k) ι | observ {t} {k} = arbitrary ([[ t ]] μF → k)
rndArg μF .(t ==> var) ι | constr {t} = ι


-- Gives the type to use for the type variable
monotype : (t : Type) -> Set
monotype t = (fix (Functor t))

-- The test case generator "profile"
testArg : (t : Type) -> [[ t ]] (monotype t)
testArg t = rndArg (fix (Functor t)) t In



filterArgs = cross (var ==> con Bool) (list var) 

-- test by evaluating: 
--     monotype  filterArgs
--     testArg   filterArgs


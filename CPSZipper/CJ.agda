module CJ2 where

open import Data.Nat
open import Data.Maybe
open import Data.Fin
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality1
  

data Funct : ℕ -> Set1 where
  K : forall n -> Set -> Funct n
  _⊕_ : forall {n} -> Funct n -> Funct n -> Funct n
  _⊗_ : forall {n} -> Funct n -> Funct n -> Funct n
  π : forall {n} -> Fin n -> Funct n

-- Id = π 0
-- Fst = π 0
-- Snd = π 1


weaken : forall {n} -> Bool -> Funct n -> Funct (suc n)
weaken n (K o s) = K (suc o) s
weaken true (π i) = π (inject₁ i)
weaken false (π i) = π (suc i)
weaken n (p ⊕ q) = weaken n p ⊕ weaken n q
weaken n (p ⊗ q) = weaken n p ⊗ weaken n q

◃ = weaken true
▷ = weaken false


Zero : forall n -> Funct n
Zero n = K n ⊥

One : forall n -> Funct n
One n = K n ⊤


Fun : ℕ -> Set1
Fun 0 = Set
Fun (suc n) = Set -> Fun n

consts : (n : ℕ) -> Set -> Fun n
consts 0 s = s
consts (suc n) s = \_ -> consts n s 

lift2 : {n : ℕ} -> (Set -> Set -> Set) -> Fun n -> Fun n -> Fun n
lift2 {0} _x_ l r = l x r
lift2 {suc n} _x_ l r = \t -> lift2 _x_ (l t) (r t)


sem : forall n -> Funct n -> Fun n
sem zero (K .0 y) = y
sem (suc n) (K .(suc n) y) = \t -> sem n (K n y)
sem n (p ⊕ q) = lift2 _⊎_ (sem n p) (sem n q)
sem n (p ⊗ q) = lift2 _×_ (sem n p) (sem n q)
sem .(suc n) (π (zero {n})) = consts n
sem .(suc n) (π (suc {n} i)) = \t -> sem n (π i)

[[_]] : forall {n} -> Funct n -> Fun n
[[_]] {n} f = sem n f

lemma< : (q : Funct 1) (x y : Set) -> sem 2 (weaken true q) x y ≡₁ sem 1 q x
lemma< (K .1 _) x y = ≡₁-refl
lemma< (p ⊕ q) x y = ≡₁-cong₂ _⊎_ (lemma<  p x y) (lemma<  q x y)
lemma< (p ⊗ q) x y = ≡₁-cong₂ _×_ (lemma<  p x y) (lemma<  q x y)
lemma< (π zero) x y = ≡₁-refl
lemma< (π (suc ())) x y

lemma> : (q : Funct 1) (x y : Set) -> sem 2 (weaken false q) x y ≡₁ sem 1 q y
lemma> (K .1 _) x y = ≡₁-refl
lemma> (p ⊕ q) x y = ≡₁-cong₂ _⊎_ (lemma>  p x y) (lemma>  q x y)
lemma> (p ⊗ q) x y = ≡₁-cong₂ _×_ (lemma>  p x y) (lemma>  q x y)
lemma> (π zero) x y = ≡₁-refl
lemma> (π (suc ())) x y

if1_then_else_ : {a : Set1} -> Bool -> a -> a -> a
if1 true  then t else f = t
if1 false then t else f = f


lemma : forall dir -> (q : Funct 1) (x y : Set) -> sem 2 (weaken dir q) x y ≡₁ sem 1 q (if1 dir then x else y)
lemma true q x y = lemma< q x y 
lemma false q x y = lemma> q x y

lem : {q : Funct 1} {dir : Bool}  {x y : Set} -> sem 2 (weaken dir q) x y ≡₁ sem 1 q (if1 dir then x else y)
lem {q} {dir} {x} {y} = lemma dir q x y


△ : Funct 1 -> Funct 2
△ (K .1 y) = Zero 2
△ (p ⊕ q) = △ p ⊕ △ q
△ (p ⊗ q) = (△ p ⊗ ▷ q) ⊕ (◃ p ⊗ △ q)
△ (π zero) = One 2
△ (π (suc ()))

mindp : forall {j pd pc x y} ->  ( j × pd ) ⊎ pc -> j × ( pd ⊎ x) ⊎ ( pc ⊎ y )
mindp (inj₁ (j , pd)) = inj₁ (j , inj₁ pd)
mindp (inj₂ pc) = inj₂ (inj₁ pc)

mindq : forall {j qd qc x y} ->  ( j × qd ) ⊎ qc -> (j × ( x ⊎ qd)) ⊎ ( y ⊎ qc )
mindq (inj₁ (j , qd)) = inj₁ (j , inj₂ qd)
mindq (inj₂ qc) = inj₂ (inj₂ qc)


cvt : forall {x y : Set} -> x ≡₁ y -> (a : x) -> y
cvt ≡₁-refl a = a

mutual 
  mndp : forall p q -> forall {c j} -> (j × [[ △ p ]] c j) ⊎ [[ p ]] c -> [[ q ]] j -> (j × [[ △ (p ⊗ q) ]] c j) ⊎ [[ (p ⊗ q) ]] c
  mndp p q (inj₁ (j , pd)) qj = inj₁ (j , inj₁ (pd , cvt (≡₁-sym (lem {q})) qj))
  mndp p q (inj₂ pc) qj = mndq p q pc (right q (inj₁ qj))

  mndq : forall p q -> forall {c j} -> [[ p ]] c -> (j × [[ △ q ]] c j) ⊎ [[ q ]] c -> (j × [[ △ (p ⊗ q) ]] c j) ⊎ [[ (p ⊗ q) ]] c
  mndq p q pc (inj₁ (j , qd)) = inj₁ (j , inj₂ ( cvt (≡₁-sym (lem {p})) pc , qd))
  mndq p q pc (inj₂ qc) = inj₂ ( pc , qc)

  right : forall {j c : Set} -> (p : Funct 1) -> ([[ p ]] j ⊎ ([[ △ p ]] c j × c)) -> (j × [[ △ p ]] c j) ⊎ [[ p ]] c
  right (K .1 y) (inj₁ x) = inj₂ x
  right (K .1 y) (inj₂ (() , y'))
  right (p ⊕ q) (inj₁ (inj₁ pj)) = mindp (right p (inj₁ pj))
  right (p ⊕ q) (inj₁ (inj₂ qj)) = mindq (right q (inj₁ qj))
  right (p ⊕ q) (inj₂ (inj₁ pd , c)) = mindp (right p (inj₂ (pd , c)))
  right (p ⊕ q) (inj₂ (inj₂ qd , c)) = mindq (right q (inj₂ (qd , c)))
  right (p ⊗ q) (inj₁ (pj , qj)) = mndp p q (right p (inj₁ pj)) qj 
  right (p ⊗ q) (inj₂ (inj₁ (pd , qj) , c)) = mndp p q (right p (inj₂ (pd , c))) (cvt (lem {q}) qj)
  right (p ⊗ q) (inj₂ (inj₂ (pc , qd) , c)) = mndq p q (cvt (lem {p}) pc) (right q (inj₂ (qd , c))) 
  right (π zero) (inj₁ j) = inj₁ (j , tt)
  right (π zero) (inj₂ (tt , c)) = inj₂ c
  right (π (suc ())) x


∂ : Funct 1 -> Fun 1
∂ p x = [[ △ p ]] x x


plug : forall {x} -> (p : Funct 1) -> x -> ∂ p x -> [[ p ]] x
plug (K .1 y)     x ()
plug (p ⊕ q) x (inj₁ pd) = inj₁ (plug p x pd)
plug (p ⊕ q) x (inj₂ pq) = inj₂ (plug q x pq)
plug {X} (p ⊗ q) x (inj₁ (pd , qx)) = plug p x pd , cvt (lem {q}) qx 
plug {X} (p ⊗ q) x (inj₂ (px , qd)) = cvt (lem {p}) px , (plug q x qd)
plug (π zero)     x tt = x
plug (π (suc ())) x z

data μ (p : Funct 1) : Set where
  In : [[ p ]] (μ p) -> μ p

Move : Set1
Move = (p : Funct 1) -> (μ p × List (∂ p (μ p))) -> Maybe (μ p × List (∂ p (μ p)))

zUp : Move
zUp p (t , []) = nothing
zUp p (t , pd ∷ pds) = just (In (plug p t pd), pds)

zRight : Move
zRight p (x , []) = nothing
zRight p (t , pd ∷ pds) with right p (inj₂ (pd , t)) 
... | (inj₁ (t' , pd')) = just (t' , pd' ∷ pds)
... | (inj₂ _) = nothing


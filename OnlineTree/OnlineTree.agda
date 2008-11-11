

module OnlineTree where

import Relation.Binary.EqReasoning

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Vec
open import Data.Product
open import Relation.Binary.PropositionalEquality



Nat = ℕ

open Relation.Binary.EqReasoning (≡-setoid Nat)

factor = 2
initial = 2

True = ⊤

_-_ : Nat -> Nat -> Nat
zero - n = zero
n - zero = n
suc n - suc m = n - m
infixl 1 _-_

lemma-sub : forall n -> (n - 0) ≡ n
lemma-sub zero = ≡-refl
lemma-sub (suc n) = ≡-refl

min = _⊓_



lemma-min : forall n -> zero ≡ min n zero
lemma-min zero = ≡-refl
lemma-min (suc n) = ≡-refl

⊓-assoc : forall a b c -> (a ⊓ b) ⊓ c  ≡ a ⊓ (b ⊓ c) 
⊓-assoc zero b c = ≡-refl
⊓-assoc (suc n) zero c = ≡-refl
⊓-assoc (suc n) (suc n') zero = ≡-refl
⊓-assoc (suc a) (suc b) (suc c) = ≡-cong suc (⊓-assoc a b c)

max : Nat -> Nat -> Nat
max zero n = n
max m zero = m
max (suc m) (suc n) = suc (max m n)

data Tree (a : Set) (maxLeftSize : Nat) : (size : Nat) -> Set where
  Leaf : Tree a maxLeftSize 0
  Node : forall size-1 -> 
          let leftSize = min maxLeftSize (size-1)
              rightSize = size-1 - leftSize in
         a -> Tree a initial leftSize -> Tree a (maxLeftSize * factor) rightSize -> 
         Tree a maxLeftSize (1 + size-1)

measure : forall {a maxLeftSize size} -> Tree a maxLeftSize size -> Nat
measure Leaf = 0
measure {a} {maxLeftSize} (Node _ _ l r) = 1 + measure l + measure r




thm-0 : forall n m -> min m n + (n - min m n) ≡ n
thm-0 zero m = ≡-cong (\x -> x + 0) (≡-sym (lemma-min m))
thm-0 (suc n) zero = ≡-refl
thm-0 (suc n) (suc m) = ≡-cong suc (thm-0 n m)

-- The measure and the size coincide.
thm-measure : forall {a maxLeftSize} -> {size : Nat} -> (t : Tree a maxLeftSize size) -> measure t ≡ size
thm-measure Leaf = ≡-refl
thm-measure (Node size _ l r) with measure l | measure r | thm-measure l | thm-measure r
thm-measure {a} {maxLeftSize} {.(suc size-1)} (Node size-1 y l r)
  | .(min maxLeftSize (size-1))
  | .(size-1 - min maxLeftSize (size-1))
  | ≡-refl | ≡-refl
  = ≡-cong suc (thm-0 size-1 maxLeftSize)

depth : forall {a maxLeftSize size} -> Tree a maxLeftSize size -> Nat
depth Leaf = 0
depth (Node size-1 _ l r ) = 1 + max (depth l) (depth r)

lookTime : forall {a maxLeftSize size} -> Tree a maxLeftSize size -> Nat -> Nat
lookTime Leaf n = 0 -- not found
lookTime (Node size-1 _ l r) zero = 0 -- at the root
lookTime {a} {maxLeftSize} {.(suc size-1)} (Node size-1 _ l r) (suc index-1) with compare (suc index-1) maxLeftSize
lookTime {a} {.(suc (suc (index-1 + k)))} {.(suc size-1)}
  (Node size-1 _ l r)
  (suc index-1)
  | less .(suc index-1) k
  = lookTime l index-1 -- in left.
lookTime {a} {.(suc index-1)} {.(suc size-1)} (Node size-1 y l r)
  (suc index-1)
  | equal .(suc index-1)
  = lookTime l index-1
lookTime {a} {maxLeftSize} {.(suc size-1)} (Node size-1 y l r)
  (suc .(maxLeftSize + k))
  | greater .maxLeftSize k
  = lookTime r k

-- Whoops!

lemma-min-sub : forall n m -> (m - n) ≡ (m - min n m)
lemma-min-sub zero n = ≡-refl
lemma-min-sub (suc m) zero = ≡-refl
lemma-min-sub (suc m) (suc n) = lemma-min-sub m n


lemma-xs : forall n m o -> (n - m ⊓ o - (o - m ⊓ o)) ≡ (n - o)
lemma-xs zero m o = ≡-refl
lemma-xs (suc n) zero o = ≡-cong (\x -> suc n - x) (lemma-sub o)
lemma-xs (suc n) (suc n') zero = ≡-refl
lemma-xs (suc n) (suc n') (suc n0) = lemma-xs n n' n0

lemma-r : forall n m o -> ((o - m ⊓ o) ⊓ (n - m ⊓ o)) ≡ (o ⊓ n - m ⊓ (o ⊓ n))
lemma-r zero zero zero = ≡-refl
lemma-r zero zero (suc n) = ≡-refl
lemma-r zero (suc n) zero = ≡-refl
lemma-r zero (suc m) (suc o) = ≡-sym (lemma-min (o - m ⊓ o))
lemma-r (suc n) zero zero = ≡-refl
lemma-r (suc n) zero (suc n') = ≡-refl
lemma-r (suc n) (suc n') zero = ≡-refl
lemma-r (suc n) (suc m) (suc o) = lemma-r n m o

-- leftBudget = min leftSize budget-1 
toTree' : (a : Set) (n : Nat) -> (budget : Nat) -> (leftSize : Nat) -> Vec a n -> (Tree a leftSize (min budget n) × Vec a (n - budget))
toTree' a zero budget leftSize [] = ≡-subst (Tree a leftSize) (lemma-min budget) Leaf , []
toTree' a (suc n) zero leftSize xs = Leaf , xs
toTree' a (suc n) (suc budget-1) leftSize (x ∷ xs) with toTree' a n (min leftSize budget-1) initial xs 
... | (l , xs') with toTree' a (n - min leftSize budget-1) (budget-1 - min leftSize budget-1) (leftSize * factor) xs' 
... | (r , xs'' ) = Node (min budget-1 n) x 
                      (≡-subst (Tree a initial) (⊓-assoc leftSize budget-1 n) l) 
                      (≡-subst (Tree a (leftSize * factor)) (lemma-r n leftSize budget-1) r) 
                      ,
      ≡-subst (Vec a) (lemma-xs n leftSize budget-1) xs''


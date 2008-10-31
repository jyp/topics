

module OnlineTree where

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.List
open import Data.Product

Nat = ℕ

factor = 2
initial = 2

True = ⊤

data Status : Set where
  Full : Status
  Empty : Status
  Other : Status

_=/>_ : Status -> Status -> Set
Full =/> _ = True
_ =/> Empty = True
_ =/> _ = ⊥

mix : Status -> Status -> Status 
mix Full Full = Full
mix _ _ = Other

data Tree (a : Set) (leftSize : Nat) : Status -> Set where
  Leaf : Tree a leftSize Empty
  Node : forall {l r} -> 
         a -> Tree a initial l -> Tree a (leftSize * factor) r -> 
         l =/> r -> 
         Tree a leftSize (mix l r)

_::_ = _∷_

toTree' : forall {a} -> (leftSize : Nat) -> Nat -> List a -> (Tree a leftSize {! !} × List a)
toTree' _ _ [] = (Leaf , [])
toTree' budget leftsize (x ∷ xs) = {! !}

--     | budget <= 0 = (Leaf, x:xs)
--     | otherwise = let (l,xs')  = toTree' leftBugdet                initialLeftSize     xs
--                       (r,xs'') = toTree' (budget - leftBugdet - 1) (leftsize * factor) xs'
--                       -- it's possible that actual leftsize is smaller,
--                       -- but in that case xs' is null, so it does not matter.
--                       leftBugdet = min (budget - 1) leftsize
--                   in (Node x l r, xs'')
-- 
-- -- toTree = fst . toTree' maxBound initialLeftSize -- where maxBound stands for infinity.
-- 

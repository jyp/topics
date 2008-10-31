{-# OPTIONS -fglasgow-exts #-}

import Prelude hiding (sum, foldl)
import PolishParse3
import Data.Maybe
import qualified Data.Tree as S
import Control.Applicative
import Data.Traversable
import Data.Foldable

data Tree0 a = Node0 a (Tree0 a) (Tree0 a)
             | Leaf0
   deriving Show

type K a = forall b. (Tree a -> b) -> b

data Tree a = Node a (K a) (K a)
            | Leaf

factor = 2 

initialLeftSize = 2

direct :: Int -> [a] -> (Tree a -> b) -> b
direct leftSize [] k = k Leaf
direct leftSize (x:xs) k = 
  k (Node x 
     (direct initialLeftSize xl)
     (direct (leftSize * factor) xr)
    )
  where (xl, xr) = splitAt leftSize xs
        



toTree0 Leaf = Leaf0
toTree0 (Node a l r) = Node0 a (toTree0 (l id)) (toTree0 (r id))
{-# OPTIONS -fglasgow-exts #-}

import Prelude hiding (sum, foldl, drop)
import PolishParse3
import Data.Maybe
import qualified Data.Tree as S
import Control.Applicative
import Data.Traversable
import Data.Foldable

data Tree a = Node a (Tree a) (Tree a)
            | Leaf
              deriving Show

{-

Why not the more classical definition?

data Bin a = Bin (Tree a) (Tree a)
           | Leaf a
           | Nil

Leaf or Bin? 
We cannot to decide which constructor to return with a minimal look ahead!

-}

instance Traversable Tree where
    traverse f (Node x l r) = Node <$> f x <*> traverse f l <*> traverse f r
    traverse f Leaf = pure Leaf

instance Foldable Tree where
    foldMap = foldMapDefault

instance Functor Tree where
    fmap = fmapDefault

factor = 2 

initialLeftSize = 2

toTree = fst . toTree' maxBound initialLeftSize -- where maxBound stands for infinity.
(.!) = look initialLeftSize


toTree' :: Int -> Int -> [a] -> (Tree a, [a])
toTree' _ _ [] = (Leaf, [])
toTree' budget leftsize (x:xs) 
    | budget <= 0 = (Leaf, x:xs)
    | otherwise = let (l,xs')  = toTree' leftBugdet                initialLeftSize     xs
                      (r,xs'') = toTree' (budget - leftBugdet - 1) (leftsize * factor) xs'
                      -- it's possible that actual leftsize is smaller,
                      -- but in that case xs' is null, so it does not matter.
                      leftBugdet = min (budget - 1) leftsize
                  in (Node x l r, xs'')

look :: Int -> Tree a -> Int -> a
look leftsize Leaf index  = error "online tree: index out of bounds"
look leftsize (Node x l r) index 
    | index == 0 = x
    | index <= leftsize = look initialLeftSize l (index - 1)
    | otherwise = look (leftsize * factor) r (index - 1 - leftsize)

toReverseList :: Tree a -> [a]
toReverseList = foldl (flip (:)) []

type E a = a -> a

toEndo Leaf = id
toEndo (Node x l r) = (x :) . toEndo l . toEndo r

dropBut amount t = drop' initialLeftSize id t amount []
  where
    drop' :: Int -> E [a] -> Tree a -> Int -> E [a]
    drop' leftsize prec Leaf n = prec
    drop' leftsize prec t@(Node x l r) index
        | index == 0 = prec . toEndo t
        | index <= leftsize = drop' initialLeftSize     (x :)         l (index - 1)            . toEndo r
        | otherwise         = drop' (leftsize * factor) (last prec l) r (index - 1 - leftsize)
    last :: E [a] -> Tree a -> [a] -> [a]
    last prec t = case toReverseList t of
        (x:xs) -> (x :)
        _ -> prec


drop amount t = dropHelp initialLeftSize t amount []

dropHelp :: Int -> Tree a -> Int -> [a] -> [a]
dropHelp leftsize Leaf n = id
dropHelp leftsize t@(Node x l r) index
    | index == 0 = (x :) . recL 0 . recR 0
    | index <= leftsize = recL (index - 1) . recR 0
    | otherwise = recR  (index - 1 - leftsize)
  where recL = dropHelp initialLeftSize     l 
        recR = dropHelp (leftsize * factor) r


shape :: Show a => Tree a -> [S.Tree String]
shape Leaf = [] -- [S.Node "o"[]]
shape (Node x l r) = [S.Node (show x) (shape l ++ shape r)]

sz :: S.Tree a -> Int
sz (S.Node a xs) = 1 + sum (map sz xs)

trans :: (S.Tree a -> b) -> (S.Tree a -> S.Tree b)
trans f n@(S.Node x xs) = S.Node (f n) (map (trans f) xs)

ev f (S.Node x xs) = S.Node (f x) (map (ev f) xs)

parse leftSize maxSize
   | maxSize <= 0 = pure Leaf
   | otherwise 
     =  (Node <$> symbol (const True)
              <*> parse factor              (min leftSize (maxSize - 1))
              <*> parse (leftSize * factor) (maxSize - leftSize - 1))
     <|> (eof *> pure Leaf) 
    -- NOTE: eof here is important for performance (otherwise the
    -- parser would have to keep this case until the very end of input
    -- is reached.
         

--getNextItem :: Int -> P s s
getNextItem sz
    | sz <= 0 = empty
    | otherwise = symbol (const True)

tt = parse

test1 = tt factor 30 <* eof

-- main = putStrLn $ S.drawForest $ shape $ snd $ fromJust $ unP test1 [1..100]
tree = runPolish test1 [1..100]
main = putStrLn $ S.drawForest  $ shape $ tree


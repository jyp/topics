{-# OPTIONS -fglasgow-exts #-}

import Prelude hiding (sum, foldl)
import Data.Maybe
import qualified Data.Tree as S
import Control.Applicative
import Data.Traversable
import Data.Foldable
import PolishParse3

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

-- constructing the tree in "direct" style
direct :: Int -> [a] -> Tree a
direct leftSize [] = Leaf
direct leftSize (x:xs) = Node x (direct initialLeftSize xl)
                                (direct (leftSize * factor) xr)
  where (xl, xr) = splitAt leftSize xs
        
-- fuse with splitAt
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
toTree = fst . toTree' maxBound initialLeftSize -- where maxBound stands for infinity.

-- CPS toTree'
ttCPS :: Int -> Int -> [a] -> ((Tree a, [a]) -> b) -> b
ttCPS _ _ [] k = k (Leaf, [])
ttCPS budget leftsize (x:xs) k
    | budget <= 0 = k (Leaf, x:xs)
    | otherwise = ttCPS leftBugdet                initialLeftSize     xs $ \ ~(l,xs' ) ->
                  ttCPS (budget - leftBugdet - 1) (leftsize * factor) xs'$ \ ~(r,xs'') ->
                  k (Node x l r, xs'')
   where leftBugdet = min (budget - 1) leftsize

ttCPSMain :: [a] -> (Tree a, [a])
ttCPSMain list = ttCPS maxBound initialLeftSize list id

type I a = (Tree a, [a])
-- When finding the empty list, don't want to close the tree right now, but return the continuation (so we can continue :))
-- So, we want b = fctArgs * ((Tree a, [a]) -> b) + Result
-- No prolem! Just introduce a data type being the fixpoint.
data K a = K ([a] -> K a) (I a)

kk ~(K l r) = r

instance Show a => Show (K a) where
    show ~(K _ ~(t,_)) = show t

ttC :: Int -> Int -> [a] -> (I a -> K a) -> K a
-- note that the semantics of [] have changed! it now means "suspend" instead of end of list.
ttC budget leftsize [] k = K (\i -> ttC budget leftsize i k) (kk $ k (Leaf, []))
ttC budget leftsize (x:xs) k
    | budget <= 0 = k (Leaf, x:xs)
    | otherwise = ttC leftBugdet                initialLeftSize     xs $ \ ~(l,xs')  ->
                  ttC (budget - leftBugdet - 1) (leftsize * factor) xs'$ \ ~(r,xs'') ->
                  k (Node x l r, xs'')
   where leftBugdet = min (budget - 1) leftsize

initial :: K a
initial = K (\i -> ttC maxBound initialLeftSize i fin) (Leaf, [])

-- stabilise and return the result always.
fin x = K (\i -> fin x) x 

continue :: [a] -> K a -> K a
continue input ~(K f _) = f input

finish :: K t -> (Tree t, [t])
finish ~(K _ t) = t

-- Defun ttCPS
data Lam a b -- (Tree a, [a]) -> b
   = Lam2 -- \r,rs'' -> k (Node x l r, xs'')
     (Lam a b) -- k
     a -- x
     (Tree a) -- l
   | Lam1 -- \l,xs' ...
     Int -- bugget
     Int -- leftSize
     (Lam a b) -- k
     a -- x
   | End (Tree a -> b)


ttDef :: Int -> Int -> [a] -> (Lam a b) -> b
ttDef _ _ [] k = apply k (Leaf, [])
ttDef budget leftSize (x:xs) k
    | budget <= 0 = apply k (Leaf, x:xs)
    | otherwise = ttDef (lb budget leftSize) initialLeftSize xs $ (Lam1 budget leftSize k x)

apply (Lam2                 k x l) (r,xs'') = apply k (Node x l r, xs'')
apply (Lam1 bugget leftSize k x) (l, xs') = ttDef (bugget - lb bugget leftSize - 1) (leftSize * factor) xs' (Lam2 k x l)
apply (End extract) (result,xs) = extract result

lb bugget leftSize = min (bugget - 1) leftSize

index = flip (.!)

(.!) = look initialLeftSize
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


dropTopLevel amount t = dropHelp initialLeftSize t amount []

dropHelp :: Int -> Tree a -> Int -> [a] -> [a]
dropHelp leftsize Leaf n = id
dropHelp leftsize t@(Node x l r) index
    | index == 0 = (x :) . recL 0 . recR 0
    | index <= leftsize = recL (index - 1) . recR 0
    | otherwise = recR  (index - 1 - leftsize)
  where recL = dropHelp initialLeftSize     l 
        recR = dropHelp (leftsize * factor) r


shape :: Show a => Tree a -> [S.Tree String]
shape Leaf = []
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

disp t = putStrLn $ S.drawForest  $ shape $ t

-- main = putStrLn $ S.drawForest $ shape $ snd $ fromJust $ unP test1 [1..100]

tree = runPolish test1 [1..100]
main = disp $ tree


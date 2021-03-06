{-# OPTIONS -fglasgow-exts #-}

import Prelude hiding (sum, foldl, drop)
import qualified Prelude
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

-- constructing the tree in "direct" style
direct :: Int -> [a] -> Tree a
direct leftSize [] = Leaf
direct leftSize (x:xs) = Node x (direct initialLeftSize (take leftSize xs)) 
                                (direct (leftSize * factor) (Prelude.drop leftSize xs))

-- expand in the drop
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

-- CPS toTree'
ttCPS :: Int -> Int -> [a] -> ((Tree a, [a]) -> b) -> b
ttCPS _ _ [] k = k (Leaf, [])
ttCPS budget leftsize (x:xs) k
    | budget <= 0 = k (Leaf, x:xs)
    | otherwise = ttCPS leftBugdet                initialLeftSize     xs $ \(l,xs')  ->
                  ttCPS (budget - leftBugdet - 1) (leftsize * factor) xs'$ \(r,xs'') ->
                  k (Node x l r, xs'')
   where leftBugdet = min (budget - 1) leftsize

ttCPSMain :: [a] -> (Tree a, [a])
ttCPSMain list = ttCPS maxBound initialLeftSize list id


data Expr s a where
    Val :: !a -> Expr s a
    App :: Expr s (a -> b) -> Expr s a -> Expr s b
    Abs :: (a -> Expr s b) -> Expr s (a -> b)
    Suspend ::(s -> Expr s a) -> Expr s a ->  Expr s a

instance Show (Expr s a) where
    showsPrec d (Val x) = showString "."
    showsPrec d (Abs f) = showString "\\"
    showsPrec d (App t1 t2) = showParen (d > 1) (showsPrec 1 t1 . showString " " . showsPrec 2 t2)
    showsPrec d (Suspend _ _) = showString "?"

instance Show (a -> b) where
    show _ = "<function>"

instance Applicative (Expr s) where
    (<*>) = App
    pure = Val

instance Functor (Expr s) where
    fmap f = (pure f <*>) 

let_ :: Expr s a -> (a -> Expr s b) -> Expr s b
let_ value binder = Abs binder <*> value

ttE :: Int -> Int -> Expr [a] ([a] -> (Tree a, [a]))
ttE budget leftSize = Abs $ 
   let susp = \input ->
        if budget <= 0 then pure (Leaf, input)
        else case input of 
                   [] -> Suspend susp (pure (Leaf, []))
                   (x:xs) -> let_ (ttE leftBugdet                initialLeftSize     <*> pure xs ) $ \(l,xs') ->
                             let_ (ttE (budget - leftBugdet - 1) (leftSize * factor) <*> pure xs') $ \(r,xs'') ->
                             pure (Node x l r, xs'')
   in susp
 where leftBugdet = min (budget - 1) leftSize 

ttX = ttE maxBound initialLeftSize

eval :: Expr s a -> a
eval (Val v) = v
eval (App f x) = (eval f) (eval x)
eval (Abs f) = \a -> eval (f a)
eval (Suspend _ finish) = eval finish

appVal :: Expr s (s -> b) -> s -> Expr s (s -> b)
appVal e v = case evalP $ e <*> pure v of 
    Left f -> Abs f

-- Partially evaluate an expression.
evalP :: Expr s a -> Either (s -> Expr s a) (Expr s a)
evalP (Suspend s _) = Left s -- by definition
evalP (Val v) = Right (Val v)
evalP (App f0 x0) = case evalP f0 of
    Left f -> Left (\s -> evalQ (f s <*> x0))
    Right f -> case evalP x0 of
        Left x -> Left (\s -> evalQ (f <*> x s))
        Right x -> Right (evalQ (f <*> x))
 
evalP (Abs f) = Right (Abs f)

-- Evaluate an expression as far as possible
evalQ :: Expr s a -> Expr s a
evalQ (Suspend s v) = (Suspend s v) 
evalQ (Abs f) = Abs f -- no evaluation "under lambda"
evalQ (Val v) = Val v
evalQ (App f0 x0) = case evalQ f0 of
    Val f -> case evalQ x0 of
        Val x -> Val (f x)
        x -> f <$> x
    Abs f -> case evalQ x0 of
        Val x -> evalQ (f x)
        x -> Abs f <*> x
    f -> f <*> x0



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
main = disp tree


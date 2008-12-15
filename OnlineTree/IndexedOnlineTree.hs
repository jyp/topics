{-# OPTIONS -fglasgow-exts #-}

import PolishParse3
import Data.Maybe
import qualified Data.Tree as S
import Control.Applicative

data Tree a = Node a (Tree a) (Tree a)
            | Leaf
              deriving Show

instance Traversable Tree where
    traverse f (Node x l r) = Node <$> f x <*> traverse f l <*> traverse f r
    traverse f Leaf = pure Leaf

instance Foldable Tree where
    foldMap = foldMapDefault

instance Functor Tree where
    fmap = fmapDefault


factor = 2
initialSize = 5

shape :: Show a => Tree a -> [S.Tree String]
shape Leaf = [] -- [S.Node "o"[]]
shape (Node x l r) = [S.Node (show x) (shape l ++ shape r)]

trans :: (S.Tree a -> b) -> (S.Tree a -> S.Tree b)
trans f n@(S.Node x xs) = S.Node (f n) (map (trans f) xs)

ev f (S.Node x xs) = S.Node (f x) (map (ev f) xs)

-- leftBound, rightBound
parse leftSize lB rB
   | rB <= lB = pure Leaf
   | otherwise 
     =   Node <$> symbolBefore rB
              <*> parse factor               lB   midB
              <*> parse (leftSize * factor)  midB rB
        <|> (isAfter rB *> pure Leaf) 
  where midB = min rB (lB + leftSize)
    -- NOTE: eof (isAfter) here is important for performance (otherwise the
    -- parser would have to keep this case until the very end of input
    -- is reached.
         

symbolBefore rB = symbol (< rB)

isAfter rB = symbol (>= rB)


--getNextItem :: Int -> P s s
getNextItem sz
    | sz <= 0 = empty
    | otherwise = symbol (const True)

test1 = parse initialSize 0 40 <* symbol (== 41)

sym x = symbol (== x)

-- main = putStrLn $ S.drawForest $ shape $ snd $ fromJust $ unP test1 [1..100]
tree = runPolish test1 [1..100]
main = putStrLn $ S.drawForest  $ shape $ tree


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


{-
newtype P s a = P ([s] -> Maybe ([s], a))

unP (P f) ss = f ss


instance Functor (P s) where
    fmap f (P x) = P $ \i -> case x i of
                               Nothing -> Nothing
                               Just (i', xx) -> Just (i', f xx)

instance Applicative (P s) where
    pure x = P $ \i -> Just (i,x)
    (P f) <*> (P x) = P $ \i -> case f i of
                      Nothing -> Nothing
                      Just (i', ff) -> let ~(Just (i'',xx)) = x i' 
                                         -- notice the rhs of <*> can never fail.
                                       in Just (i'',ff xx)
                      
                           

instance Alternative (P s) where
    empty = P $ \i -> Nothing
    (P x) <|> (P y) = P $ \i -> case x i of
                      Nothing -> y i
                      r -> r

getItem :: P s s
getItem = P $ \ i -> case i of
                       [] -> Nothing
                       (x:xs) -> Just (xs, x)

-}


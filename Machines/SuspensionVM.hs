-- Copyright (c) JP Bernardy 2008

{-# OPTIONS -fglasgow-exts #-}
module SuspensionVM where
import Control.Applicative
import Data.Foldable
import Data.Traversable
import Data.List hiding (map, minimumBy)
import Data.Char
import Data.Maybe (listToMaybe)

data Void

data a :< b = a :< b 

hd (a :< _) = a

infixr :<


data Steps s r where
    Val   :: a -> Steps s r               -> Steps s (a :< r)
    App   :: (Steps s ((b -> a) :< b :< r))      -> Steps s (a :< r)
    Done  ::                               Steps s Void
    Suspend :: Steps s r -> (s -> Steps s r) -> Steps s r
    -- note1. the similarity with list-eliminator
    -- note2. the 1st argument should not be suspendable at all!
    -- note3. the 2nd argument cannot depend on the tail of the list,
    -- because this will be provided in further steps.

-- | Right-eval with input
evalR :: [s] -> Steps s r -> r
evalR ss (Val a r) = a :< evalR ss r
evalR ss (App s) = (\(f:< ~(a:<r)) -> f a :< r) (evalR ss s)
evalR [] (Suspend nil cons) = evalR [] nil
evalR (s:ss)(Suspend nil cons) = evalR ss (cons s)

-- | A computation segment
newtype P s a = P {fromP :: forall r. Steps s r  -> Steps s (a :< r)}


instance Functor (P s) where
    fmap f x = pure f <*> x

instance Applicative (P s) where
    P f <*> P x = P (\fut -> (App (f (x fut))))
    pure x = P (\fut -> Val x $ fut)

-- | Pre-compute a left-prefix of some steps (as far as possible)
evalL :: Steps s a -> Steps s a
evalL (Val x r) = Val x (evalL r)
evalL (App f) = case evalL f of
                  (Val a (Val b r)) -> Val (a b) r
                  (Val f1 (App (Val f2 r))) -> App (Val (f1 . f2) r)
                  r -> App r
evalL x = x


evalLAll :: Steps s a -> [s] -> [Steps s a]
evalLAll = scanl (\c -> evalL . pushOne c)


pushEof :: Steps s a -> Steps s a
pushEof (Val x s) = Val x (pushEof s)
pushEof (App f) = App (pushEof f)
pushEof (Suspend nil cons) = pushEof nil


pushOne :: Steps s a -> s -> Steps s a
pushOne (Val x s)          ss = Val x (pushOne s ss)
pushOne (App f)            ss = App (pushOne f ss)
pushOne (Suspend nil cons) s  = cons s


pushSyms :: [s] -> Steps s a -> Steps s a
pushSyms [] x = x
pushSyms ss (Val x s) = Val x (pushSyms ss s)
pushSyms ss (App f) = App (pushSyms ss f)
pushSyms (s:ss) (Suspend nil cons) = pushSyms ss (cons s)


--------------
-- Example: Online Tree

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

case_ :: P s a -> (s -> P s a) -> P s a
case_ (P nil) cons = P $ \fut -> Suspend (nil fut) (\s -> fromP (cons s) fut)

instance Foldable Tree where
    foldMap = foldMapDefault

instance Functor Tree where
    fmap = fmapDefault


toTree leftSize maxSize
   | maxSize <= 0 = pure Leaf
   | otherwise = case_ (pure Leaf) $
       \x -> Node <$> pure x
                  <*> toTree factor              (min leftSize (maxSize - 1))
                  <*> toTree (leftSize * factor) (maxSize - leftSize - 1)

factor = 2 
initialLeftSize = 2

tt :: P s (Tree s)
tt = toTree initialLeftSize (maxBound :: Int)
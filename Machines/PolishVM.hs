-- Copyright (c) JP Bernardy 2008

{-# OPTIONS -fglasgow-exts #-}
module PolishVM where
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


data Steps r where
    Val   :: a -> Steps r               -> Steps (a :< r)
    App   :: (Steps ((b -> a) :< b :< r))      -> Steps (a :< r)
    Done  ::                               Steps Void

-- | Right-eval with input
evalR :: Steps r -> r
evalR (Val a r) = a :< evalR r
evalR (App s) = (\(f:< ~(a:<r)) -> f a :< r) (evalR s)


-- | A computation segment
newtype P s a = P {fromP :: forall r. Steps r  -> Steps (a :< r)}


instance Functor (P s) where
    fmap f x = pure f <*> x

instance Applicative (P s) where
    P f <*> P x = P (\fut -> (App (f (x fut))))
    pure x = P (\fut -> Val x $ fut)

-- | Pre-compute a left-prefix of some steps (as far as possible)
evalL :: Steps a -> Steps a
evalL (Val x r) = Val x (evalL r)
evalL (App f) = case evalL f of
                  (Val a (Val b r)) -> Val (a b) r
                  (Val f1 (App (Val f2 r))) -> App (Val (f1 . f2) r)
                  r -> App r
evalL x = x


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


-- The zipper for efficient evaluation:

-- Arbitrary expressions in Reverse Polish notation.
-- This can also be seen as an automaton that transforms a stack.
-- RPolish is indexed by the types in the stack consumed by the automaton.
data RPolish input output where
  RVal :: a -> RPolish (a :< rest) output -> RPolish rest output
  RApp :: RPolish (b :< rest) output -> RPolish ((a -> b) :< a :< rest) output 
  RStop :: RPolish rest rest

-- Evaluate the output of an RP automaton, given an input stack
evalRP :: RPolish input output -> input -> output
evalRP RStop acc = acc 
evalRP (RVal v r) acc = evalRP r (v :< acc)
evalRP (RApp r) (f :< a :< acc) = evalRP r (f a :< acc)


-- execute the automaton as far as possible
simplify :: RPolish s output -> RPolish s output
simplify (RVal a (RVal f (RApp r))) = simplify (RVal (f a) r)
simplify x = x

-- Gluing a Polish expression and an RP automaton.
-- This can also be seen as a zipper of Polish expressions.
data Zip output where
   Zip :: RPolish stack output -> Steps stack -> Zip output
   -- note that the Stack produced by the Polish expression matches
   -- the stack consumed by the RP automaton.

-- Move the zipper to the right, if possible.  The type gives evidence
-- that this function does not change the (type of) output produced.
right :: Zip output -> Zip output
right (Zip l (Val a r)) = Zip (RVal a l) r
right (Zip l (App r)) = Zip (RApp l) r
right (Zip l s) = (Zip l s)


evalZ :: Zip output -> output
evalZ (Zip rp p) = evalRP rp (evalR p)


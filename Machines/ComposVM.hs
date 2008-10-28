-- Copyright (c) JP Bernardy 2008

{-# OPTIONS -fglasgow-exts -Wall #-}
import Control.Applicative

data Void

-- Code for the machine
data Steps r where
    X    :: (r -> r') -> Steps r -> Steps r'
    Done :: Steps Void


-- | Right-eval with input
evalR :: Steps r -> r
evalR (X f r) = f (evalR r)
evalR Done = error "VM stack overflow"

-- | Pre-compute a left-prefix of some steps (as far as possible)
evalL :: Steps a -> Steps a
evalL (X f (X g s)) = evalL (X (f . g) s)
evalL x = x


-- Translating applicative language into the codes.

-- The data will be a stack that we can transform.
data a :< b = (:<) { hd :: a, tl :: b }

infixr :<

apply :: Steps ((b -> a) :< b :< r) -> Steps (a :< r)
apply = X $ \(f :< ~(a :< r)) -> f a :< r

push :: a -> Steps r -> Steps (a :< r)
push a = X (a :<)

newtype P s a = P {fromP :: forall r. Steps r  -> Steps (a :< r)}

instance Functor (P s) where
    fmap f x = pure f <*> x

instance Applicative (P s) where
    P f <*> P x = P (\fut -> (apply (f (x fut))))
    pure x = P (\fut -> push x $ fut)



{-# LANGUAGE GADTs #-}
{-# OPTIONS -fglasgow-exts #-}

import Control.Applicative


data Ter a where
     Lam :: (Ter a -> Ter b) -> Ter (a -> b)
     App :: Ter (a -> b) -> Ter a -> Ter b
     Con :: a -> Ter a

data Term a where
     Lamb :: State t -> (Term a -> Term b) -> Term (a -> b)
     Appl :: State t -> Term (a -> b) -> Term a -> Term b
     Cons :: State t -> a -> Term a


the current arg will be put in a lam; entered later.
--> need to remember where to store the state upon entering the arg.
--> this is the rhs of the Appl.

cbnExec :: State t -> t
cbnExec (State (App t1 t2) s)      = cbnExec (State t1 (Cons t2 s))
cbnExec (State (Lam f) (Cons a s)) = cbnExec (State (f a) s)
cbnExec (State (Lam f) Nil) = \x -> cbnExec (State (f (Con x)) Nil)
-- this is a rule that cannot be in the untyped version.
cbnExec (State (Con x) s) = app x s



instance Functor Term where
     fmap f = (pure f <*>)

instance Applicative Term where
   pure = Con
   (<*>) = App


----------------------------
-- Direct evaluation

eval :: Term t -> t
eval (App t1 t2) = eval t1 (eval t2)
eval (Lam f) = \x -> eval (f (Con x))
eval (Con x) = x



instance Monad Term where
    return = Con
    k >>= f = f (eval k)







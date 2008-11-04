{-# LANGUAGE GADTs #-}

import Control.Applicative


data Term a where
     Lam :: (Term a -> Term b) -> Term (a -> b)
     App :: Term (a -> b) -> Term a -> Term b
     Con :: a -> Term a
     Sto :: Term a -> Term a
     Mat :: (a -> Term b) -> Term (a -> b)

instance Functor Term where
     fmap f = (pure f <*>)

instance Applicative Term where
   pure = Con
   (<*>) = App


data State output where
   State :: Term fct -> Stack fct output -> State output

data Stack fct output where
    Nil :: Stack output output
    Cons :: Term a -> Stack fct output -> Stack (a -> fct) output

step :: State t -> State t
step (State (App t1 t2) s)      = State t1 (Cons t2 s)
step (State (Lam f) (Cons a s)) = State (f a) s

eval = fullEval . state

fullEval :: State t -> t
fullEval (State (App t1 t2) s)      = fullEval (State t1 (Cons t2 s))
fullEval (State (Lam f) (Cons a s)) = fullEval (State (f a) s)
fullEval (State (Lam f) Nil) = \x -> fullEval (State (f (Con x)) Nil)
fullEval (State (Con x) s) = app x s
fullEval (State (Mat f) (Cons a s)) = fullEval (State (Con (f a)) s)
fullEval (State (Mat f) Nil) = \x -> eval (f x)

app :: fct -> Stack fct output -> output
app x s = case s of
    Nil -> x
    (Cons y z) -> app (x (fullEval (State y Nil))) z

state t = State t Nil



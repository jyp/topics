{-# OPTIONS -fglasgow-exts #-}
-- This is inspired by Ryan Ingram
-- http://www.haskell.org//pipermail/haskell-cafe/2008-November/050768.html

import Data.Char

data Term v t where
   Var :: v t -> Term v t
   App :: Term v (a -> b) -> Term v a -> Term v b
   Lam :: (v a -> Term v b) -> Term v (a -> b)

newtype Exp t = Exp (forall v. Term v t)

-- An evaluator
eval :: Exp t -> t
eval (Exp e) = evalP e

newtype Id a = Id {fromId :: a}

evalP :: Term Id t -> t
evalP (Var (Id a)) = a
evalP (App e1 e2) = evalP e1 $ evalP e2
evalP (Lam f) = \a -> evalP (f (Id a))

-- Using "show" to peek inside functions!

newtype K t a = K t

show' :: Int -> Term (K Int) t -> String
show' _ (Var (K c)) = [chr (ord 'a' + c)]
show' d (App f x) = show' d f ++ " " ++ show' d x
show' d (Lam a) = show' (d+1) (a (K d))



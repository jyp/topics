{-# LANGUAGE GADTs #-}
{-# OPTIONS -fglasgow-exts #-}

import Control.Applicative


data Term input output where
     App :: Term input (a -> b) -> Term input a -> Term input b
     Con :: a -> Term input a

     Disj :: Term f c -> Term g c -> Term (f :+: g) c
     Conj :: Term (f a -> g a -> c) -> Term (f :*: g) c
     Kons :: (x -> Term c) -> Term (K x a -> c)
     Wrap :: Term (f (T f) -> c) -> Term ((T f) -> c)


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
eval (Disj f g) = \x -> case x of
    Inl a -> eval (f <*> pure a)
    Inr a -> eval (g <*> pure a)
eval (Conj f) = \(x :*: y) -> eval (f <*> pure x <*> pure y)


instance Monad Term where
    return = Con
    k >>= f = f (eval k)

data T (f :: * -> *) where
    In :: f (T f) -> T f
out (In x) = x

infixr :+:
data (:+:) f g a where
    Inl :: f a -> (:+:) f g a
    Inr :: g a -> (:+:) f g a

instance (Functor f, Functor g) => Functor (f :+: g) where
    fmap h (Inl x) = Inl (fmap h x)
    fmap h (Inr x) = Inr (fmap h x)

infixr :*:
data (:*:) f g a where
    (:*:) :: f a -> g a -> (:*:) f g a

instance (Functor f, Functor g) => Functor (f :*: g) where
    fmap h (x :*: y) = fmap h x :*: fmap h y

data K x a = K {fromK :: x}
instance Functor (K x) where
    fmap f (K x) = K x

data Id a = Id {fromId :: a}
instance Functor (Id) where
    fmap f (Id a) = Id (f a)

type List x = T (K () :+: (K x :*: Id))

prod :: Term (List Int -> Int)
prod = Wrap $ Disj
       (Kons $ \_ -> pure 1)
       (Conj $ Lam $ \x -> Lam $ \xs -> (*) <$> (fromK <$> x) <*> (prod <*> (fromId <$> xs)))




---------------------------
-- Data-driven evaluation

deval 
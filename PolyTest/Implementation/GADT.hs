{-# LANGUAGE TypeFamilies, EmptyDataDecls, GADTs, TypeOperators, FlexibleInstances #-}

data Poly a t where
    Var :: Poly a a
    Fun :: Poly a t -> Poly a u -> Poly a (t -> u)
    Con :: Z1 t -> Poly a t
    


newtype Fix f = In { out :: f (Fix f)}

data Z1 a
data Id a = Id a
data K x a = K x
data (f :+: g) a = L1 (f a) | L2 (g a)
data (f :*: g) a = f a :*: g a


functorOf :: Poly a t -> 
{-# LANGUAGE TypeOperators #-}

-- Copied directly from McBride's  Jokers & Clowns.

data K2 a x y = K2 a
data Fst x y = Fst x
data Snd x y = Snd y
data (p :+ q) x y =  L2 (p x y) | R2 (q x y)
data (p :* q) x y = (p x y) :* (q x y)
type T12 = K2 ()

class Bifunctor p where
    bimap :: (s1 -> t1) -> (s2 -> t2) -> p s1 s2 -> p t1 t2

instance Bifunctor (K2 a) where
    bimap f g (K2 a) = K2 a

instance Bifunctor Fst where
    bimap f g (Fst x) =Fst (f x)

instance Bifunctor Snd where
    bimap f g (Snd y) = Snd (g y)

instance (Bifunctor p,Bifunctor q) => Bifunctor (p :+ q) where
    bimap f g (L2 p) =L2 (bimap f g p)
    bimap f g (R2 q) =R2 (bimap f g q)

instance (Bifunctor p,Bifunctor q) => Bifunctor (p :* q) where
    bimap f g (p :* q) = bimap f g p :* bimap f g q


data Zero

refute :: Zero -> a
refute x = x `seq` error "we never get this far"

inflate :: Functor p ⇒ p Zero → p x
inflate = fmap refute

type T01 = K1 Zero

type T02 = K2 Zero




{-# LANGUAGE TypeOperators, EmptyDataDecls, TypeFamilies #-}

-- From Type-Indexed Data Types, pp 166..
-- Hinze, Jeuring, Löh

-- Polynomial functors
data K1 a x = K1 a
data Id a = Id a
data (p :+ q) x =  L1 (p x) | R1 (q x)
data (p :* q) x = (p x) :* (q x)      

type T11 = K1 ()

-- Constant bifunctor
data K2 a x y = K2 a

data Fst x y = Fst x
data Snd x y = Snd y

-- Sum bifunctor
data (p :++ q) x y =  L2 (p x y) | R2 (q x y)

-- Product bifunctor
data (p :** q) x y = (p x y) :** (q x y)

type T12 = K2 ()

class Bifunctor p where
    bimap :: (s1 -> t1) -> (s2 -> t2) -> p s1 s2 -> p t1 t2

instance Bifunctor (K2 a) where
    bimap f g (K2 a) = K2 a

instance Bifunctor Fst where
    bimap f g (Fst x) =Fst (f x)

instance Bifunctor Snd where
    bimap f g (Snd y) = Snd (g y)

instance (Bifunctor p,Bifunctor q) => Bifunctor (p :++ q) where
    bimap f g (L2 p) =L2 (bimap f g p)
    bimap f g (R2 q) =R2 (bimap f g q)

instance (Bifunctor p,Bifunctor q) => Bifunctor (p :** q) where
    bimap f g (p :** q) = bimap f g p :** bimap f g q


data Zero 


-- borrow the jokers and clowns to implement "lambda" forms at the type level.
newtype JJ f r c = JJ (f r)
newtype CC f r c = CC (f c)

instance Functor f => Bifunctor (CC f) where
    bimap f g (CC pc) = CC (fmap f pc)

instance Functor f => Bifunctor (JJ f) where
    bimap f g (JJ pj) = JJ (fmap g pj)


type family Context (f :: * -> *) :: (* -> * -> *)
type instance (Context Id) = Fst
type instance (Context (K1 a)) = K2 Zero
type instance (Context (p :+ q)) = Context p :++ Context q
type instance (Context (f1 :* f2)) = (Context f1 :** JJ f2) :++ (CC f1 :** Context f2)

type Fix


plug :: 
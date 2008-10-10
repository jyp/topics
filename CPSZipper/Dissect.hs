{-# LANGUAGE TypeOperators, EmptyDataDecls, TypeFamilies #-}

-- Copied directly from McBride's  Jokers & Clowns.
-- http://portal.acm.org/citation.cfm?id=1328438.1328474&coll=GUIDE&dl=GUIDE&CFID=4573058&CFTOKEN=30689630

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

refute :: Zero -> a
refute x = x `seq` error "we never get this far"

inflate :: Functor p => p Zero -> p x
inflate = fmap refute


type T01 = K1 Zero

type T02 = K2 Zero


-- All clowns (left)
data CC p c j = CC (p c)

instance Functor f => Bifunctor (CC f) where
    bimap f g (CC pc) = CC (fmap f pc)

-- All jokers (right)

data JJ p c j = JJ (p j)

instance Functor f => Bifunctor (JJ f) where
    bimap f g (JJ pj) = JJ (fmap g pj)

-- dissection: turns a functor into a bifunctor
type family DD (a :: * -> *) :: (* -> * -> *)

type instance DD (K1 a) = T02
type instance DD (Id) = T12
type instance DD (p :+ q) = DD p :++ DD q
type instance DD (p :* q) = (DD p :** JJ q) :++ (CC p :** DD q)



class Right p where
    right :: Either (p j) (DD p c j, c) -> Either (j, DD p c j) (p c)

instance Right (K1 a) where
    right (Left (K1 a))     = Right (K1 a)
    right (Right (K2 z, c)) = refute z

instance Right Id where
    right (Left (Id j)) = Left (j, K2 ())
    right (Right (K2 (), c)) = Right (Id c)

instance (Right p, Right q) => Right (p :+ q) where
    right x = case x of
        (Left (L1 pj)) -> mindp (right (Left pj))
        (Left (R1 qj)) -> mindq (right (Left qj))
        (Right ((L2 pd, c))) -> mindp (right (Right (pd, c)))
        (Right ((R2 qd, c))) -> mindq (right (Right (qd, c)))
        where mindp (Left (j,pd)) = Left (j, L2 pd)
              mindp (Right pc) = Right (L1 pc)
              mindq (Left (j,pd)) = Left (j, R2 pd)
              mindq (Right pc) = Right (R1 pc)
              
        
{-# LANGUAGE TypeFamilies, EmptyDataDecls, GADTs, TypeOperators, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies #-}

data True = T
data False

type Nat = Int -- sic.

data Equals a b where
    Refl :: Equals a a

-- type family Occurs a b :: *
-- type instance (a ~ b) => Occurs a b = True

data A


newtype Fix f = In { out :: f (Fix f)}

data Z1 a
data Id a = Id a
data K x a = K x
data (f :+: g) a = L1 (f a) | L2 (g a)
data (f :*: g) a = f a :*: g a

class OneArg t where
    type OneArgF t :: * -> *





instance OneArg (f -> A) where
    

class AFunctor t (aFunctor :: * -> *) | t -> aFunctor where

instance AFunctor A Id where

instance AFunctor k (K k) where

-- instance AFunctor (Either a b) where
--     type AFunctorF (Either a b) = AFunctorF a :+: AFunctorF b



class PolyTestable t where
    type ExtractedFunctor t :: * -> *
--     type MonoType t :: *

--     toMonoTest :: t -> MonoType t


instance (PolyTestable res, OneArg arg) => PolyTestable (arg -> res) where
    type ExtractedFunctor (arg -> res) = OneArgF arg :*: ExtractedFunctor res

instance PolyTestable A where
    type ExtractedFunctor A = Z1

f :: a -> a
f = undefined



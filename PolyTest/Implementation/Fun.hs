{-# LANGUAGE TypeFamilies, EmptyDataDecls, GADTs, TypeOperators, FlexibleInstances #-}

import Test.QuickCheck

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

type family SubstA t a' :: *

type instance SubstA A a' = a'
type instance SubstA Int a' = Int
type instance SubstA (a -> b) a' = SubstA a a' -> SubstA b a'

class OneArg t where
    type OneArgF t :: * -> *
    type ArgType t :: * -> *
--    con :: (OneArgF t fixPoint -> fixPoint) -> SubstA t fixPoint


instance AFunctor f => OneArg (f -> A) where
    type OneArgF (f -> A) = AFunctorF f
    type ArgType (f -> A) = SubstA (f -> A)
--    con inj = \x -> inj (aCon x)

class AFunctor t where
    type AFunctorF t :: * -> *
    aCon :: SubstA t fixPoint -> AFunctorF t fixPoint

instance AFunctor A where
    type AFunctorF A = Id
    aCon = Id

instance AFunctor Int where
    type AFunctorF Int = K Int
    aCon = K

-- instance AFunctor (Either a b) where
--     type AFunctorF (Either a b) = AFunctorF a :+: AFunctorF b
--     aCon (Left x) = aCon x


class PolyTestable t where
    type ExtractedFunctor t :: * -> *
    type Monotype t :: * -> *
    polyRun :: Gen (Monotype t initalA)


instance (PolyTestable res, OneArg arg) => PolyTestable (arg -> res) where
    type ExtractedFunctor (arg -> res) = OneArgF arg :*: ExtractedFunctor res
    type Monotype (arg -> res) initialA = SubstA ArgType arg initialA (Monotype res)

instance PolyTestable A where
    type ExtractedFunctor A = Z1
--    toMonoTest = 

f :: a -> a
f = undefined




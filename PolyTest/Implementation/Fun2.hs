{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE TypeFamilies, EmptyDataDecls, GADTs, TypeOperators, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}

import Test.QuickCheck

import Unsafe.Coerce

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

class OneArg t initialA where
    type OneArgF t :: * -> *
    type AddArgType t initialA :: * -> *

    applyOneArg :: (t -> rest) -> AddArgType t initialA rest
--    con :: (OneArgF t fixPoint -> fixPoint) -> SubstA t fixPoint

--    type AddArgType t initialA = (->) (SubstA (f) initialA) "default"


instance AFunctor f => OneArg (f -> A) initialA where
    type OneArgF (f -> A) = AFunctorF f
    type AddArgType (f -> A) initialA = Id
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


class PolyTestable t initialA where
    type ExtractedFunctor t :: * -> *
    type Monotype t initialA :: *
    polyRun :: t -> Monotype t initialA


instance (PolyTestable res initalA, OneArg arg initialA) => PolyTestable (arg -> res) initialA where
    type ExtractedFunctor (arg -> res) = OneArgF arg :*: ExtractedFunctor res
    type Monotype (arg -> res) initialA = AddArgType arg initialA (Monotype res initialA)
    polyRun f = polyRun (applyOneArg f)

instance PolyTestable A initialA where
    type ExtractedFunctor A = Z1
    type Monotype A initialA = initialA
    polyRun a = restorePoly a

restorePoly :: A -> a
restorePoly = unsafeCoerce

f :: a -> a
f = undefined




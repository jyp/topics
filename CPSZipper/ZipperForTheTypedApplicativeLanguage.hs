{-# LANGUAGE ImpredicativeTypes, ScopedTypeVariables, TypeFamilies, GADTs, EmptyDataDecls #-}

import Prelude hiding (Left, Right)

data Appl a where
    (:*:) :: Appl (a -> b) -> Appl a -> Appl b
    Pure  :: a -> Appl a


data Context hole result where
    Root :: Context hole hole
    Left :: Context hole result -> Appl a -> Context (a -> hole) result
    Right :: Appl (hole -> hole') -> Context hole' result -> Context hole result

plug :: Context hole result -> Appl hole -> Appl result
plug Root x = x
plug (Left z r) x = plug z (x :*: r)
plug (Right l z) x = plug z (l :*: x)


data Zipper result where
    Zip :: Context hole result -> Appl hole -> Zipper result

up :: Zipper a -> Zipper a
up (Zip (Left ctx b) a) = Zip ctx (a :*: b)
up (Zip (Right a ctx) b) = Zip ctx (a :*: b)
up (Zip Root _) = error "All the way up"

downLeft :: Zipper result -> Zipper result
downLeft  (Zip ctx (a :*: b)) = Zip (Left ctx b) a
downLeft  (Zip ctx (Pure x)) = error "All the way down"

downRight (Zip ctx (a :*: b)) = Zip (Right a ctx) b
downRight (Zip ctx (Pure x)) = error "All the way down"



preorder, next :: Zipper a -> Zipper a
preorder z@(Zip _ (_ :*: _)) = downLeft z
preorder z@(Zip _ (Pure _)) = next z


next z@(Zip (Left ctx r) l) = Zip (Right l ctx) r
next z@(Zip (Right l ctx) r) = next $ Zip ctx (l :*: r)

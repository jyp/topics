{-# LANGUAGE ImpredicativeTypes, ScopedTypeVariables, TypeFamilies, GADTs, EmptyDataDecls #-}

import Prelude hiding (Left, Right)

-- Applicative expressions
data Appl a where
    (:*:) :: Appl (a -> b) -> Appl a -> Appl b
    Pure  :: a -> Appl a

-- And their semantics
evalAppl :: Appl a -> a
evalAppl (f :*: x) = evalAppl f $ evalAppl x
evalAppl (Pure x) = x

-- One-hole contexts for Appl
data Context hole result where
    Root :: Context hole hole
    Left  :: Appl a              -> Context hole  result -> Context (a -> hole) result
    Right :: Appl (hole -> hole') -> Context hole' result -> Context hole       result

-- Plug a hole:
plug :: Context hole result -> Appl hole -> Appl result
plug Root x = x
plug (Left r z) x = plug z (x :*: r)
plug (Right l z) x = plug z (l :*: x)


-- Interestingly, contexts can be evaluated indepentently: 

-- (This suggests that contexts can represent any form of lambda expression with
-- one hole)
evalCtx :: Context hole result -> hole -> result
evalCtx Root = id
evalCtx (Left a ctx)  = \a_to_hole -> (evalCtx ctx) (a_to_hole (evalAppl a))
evalCtx (Right a ctx) = \hole      -> (evalCtx ctx) (evalAppl a hole)


-- Zipper = context + expr 
data Zipper result where
    Zip :: Context hole result -> Appl hole -> Zipper result

-- navigation:
up, next, downLeft, downRight, preorder :: Zipper a -> Zipper a

up (Zip (Left b ctx) a) = Zip ctx (a :*: b)
up (Zip (Right a ctx) b) = Zip ctx (a :*: b)
up (Zip Root _) = error "All the way up"

downLeft  (Zip ctx (a :*: b)) = Zip (Left b ctx) a
downLeft  (Zip ctx (Pure x)) = error "All the way down"

downRight (Zip ctx (a :*: b)) = Zip (Right a ctx) b
downRight (Zip ctx (Pure x)) = error "All the way down"

preorder z@(Zip _ (_ :*: _)) = downLeft z
preorder z@(Zip _ (Pure _)) = next z

-- helper for pre-order traversal
next z@(Zip (Left r ctx) l) = Zip (Right l ctx) r
next z@(Zip (Right l ctx) r) = next $ Zip ctx (l :*: r)


data Bin = Y Bin Bin | B

-- type of contexts
data CBin = T | L Bin CBin | R Bin CBin


specCtx :: Context Bin Bin -> CBin
specCtx (Right l ctx) = continueSpecCtx ctx (fetchContext 0 l) 

continueSpecCtx :: Context Bin Bin -> (CBin -> CBin) -> CBin
continueSpecCtx (Right l ctx) precontext = continueSpecCtx ctx (precontext (fetchContext 0 l))

continueSpecCtx :: Context Bin Bin -> (Bin -> CBin -> CBin) -> CBin
continueSpecCtx (Left r ctx) precontext = continueSpecCtx ctx (precontext (evalAppl r))

fetchContext :: 1 -> Appl (Bin -> Bin -> Bin) -> (Bin -> CBin -> CBin)
fetchContext :: 0 -> Appl (Bin -> Bin)       -> (CBin -> CBin)

-- Copyright (c) JP Bernardy 2008
{-# OPTIONS -fglasgow-exts #-}
module FullIncrParser where

import Control.Applicative
import Data.List hiding (map, minimumBy)
import Data.Char
import Data.Maybe (listToMaybe)

data a :< b = a :< b

-- | Parser specification
data Parser s a where
    Pure :: a -> Parser s a
    Appl :: Parser s (b -> a) -> Parser s b -> Parser s a

    Bind :: Parser s a -> (a -> Parser s b) -> Parser s b

    Case :: Parser s a -> (s -> Parser s a) -> Parser s a
    Empt :: Parser s a
    Disj :: Parser s a -> Parser s a -> Parser s a
    Yuck :: Parser s a -> Parser s a

-- | Parser process
data Steps s a where
    Val   :: a -> Steps s r                      -> Steps s (a :< r)
    App   :: Steps s ((b -> a) :< (b :< r))      -> Steps s (a :< r)
    Done  ::                               Steps s ()
    Shift ::           Steps s a        -> Steps s a
    Fail ::                                Steps s a
    Sus :: Steps s a -> (s -> Steps s a) -> Steps s a
    Best :: Ordering -> Progress -> Steps s a -> Steps s a -> Steps s a
    Dislike :: Steps s a -> Steps s a

-- | Push a chunk of symbols or eof in the process. This forces some suspensions.
push :: Maybe [s] -> Steps s r -> Steps s r
push (Just []) p = p  -- nothing more left to push
push ss p = case p of
                  (Sus nil cons) -> case ss of
                      Nothing -> push ss nil
                      Just [] -> p
                      Just (s:ss') -> push (Just ss') (cons s)
                  (Dislike p') -> Dislike (push ss p')
                  (Shift p') -> Shift (push ss p')
                  (Val x p') -> Val x (push ss p')
                  (App p') -> App (push ss p')
                  Done -> Done
                  Fail -> Fail
                  Best _ _ p' q' -> iBest (push ss p') (push ss q')

data Progress = PSusp | PFail | PRes Int | !Int :> Progress
    deriving Show

mapSucc PSusp = PSusp
mapSucc PFail = PFail
mapSucc (PRes x) = PRes (succ x) 
mapSucc (x :> xs) = succ x :> mapSucc xs

dislikeThreshold _ = 0

-- | Compute the combination of two profiles, as well as which one is the best.
better :: Int -> Progress -> Progress -> (Ordering, Progress)
better _ PFail p = (GT, p) -- avoid failure
better _ p PFail = (LT, p)
better _ PSusp _ = (EQ, PSusp) -- could not decide before suspension => leave undecided.
better _ _ PSusp = (EQ, PSusp)
better _ (PRes x) (PRes y) = if x <= y then (LT, PRes x) else (GT, PRes y)  -- two results, just pick the best.
better lk xs@(PRes x) (y:>ys) = if x == 0 || y-x > dislikeThreshold lk then (LT, xs) else min x y +> better (lk+1) xs ys
better lk (y:>ys) xs@(PRes x) = if x == 0 || y-x > dislikeThreshold lk then (GT, xs) else min x y +> better (lk+1) ys xs
better lk (x:>xs) (y:>ys)
    | x == 0 && y == 0 = rec -- never drop things with no error: this ensures to find a correct parse if it exists.
    | y - x > threshold = (LT, x:>xs) -- if at any point something is too disliked, drop it.
    | x - y > threshold = (GT, y:>ys)
    | otherwise = rec
    where threshold = dislikeThreshold lk
          rec = min x y +> better (lk + 1) xs ys

x +> ~(ordering, xs) = (ordering, x :> xs)

progress :: Steps s r -> Progress
progress (Val _ p) = progress p
progress (App p) = progress p
progress (Shift p) = 0 :> progress p
progress (Done) = PRes 0 -- success with zero dislikes
progress (Fail) = PFail
progress (Dislike p) = mapSucc (progress p)
progress (Sus _ _) = PSusp
progress (Best _ pr _ _) = pr


-- | Right-eval a fully defined process
evalR :: Steps s (a :< r) -> (a, Steps s r)
evalR (Val a r) = (a,r)
evalR (App s) = let (f, s') = evalR s
                    (x, s'') = evalR s'
                in (f x, s'')
evalR (Shift v) = evalR v
evalR (Fail) = error "evalR: No parse!"
evalR (Best choice _ p q) = case choice of
    LT -> evalR p
    GT -> evalR q
    EQ -> error $ "evalR: Ambiguous parse: " ++ show p ++ " ~~~ " ++ show q

instance Functor (Parser s) where
    fmap f = (pure f <*>)

instance Applicative (Parser s) where
    (<*>) = Appl
    pure = Pure

instance Alternative (Parser s) where
    (<|>) = Disj
    empty = Empt

instance Monad (Parser s) where
    (>>=) = Bind
    return = pure

type Q s a = forall h r. ((h,a) -> Steps s r)  -> (h -> Steps s r)
toQ :: Parser s a -> Q s a
toQ (Case a f) = \k h -> Sus (toQ a k h) (\s -> toQ (f s) k h)
toQ (p `Appl` q) = \k -> toQ p $ toQ q $ \((h, b2a), b) -> k (h, b2a b)
toQ (Pure a)     = \k h -> k (h, a)
toQ (Disj p q)   = \k h -> iBest (toQ p k h) (toQ q k h)
toQ (Bind p a2q) = \k -> (toQ p) (\(h,a) -> toQ (a2q a) k h)
toQ Empt = \_k _h -> Fail
toQ (Yuck p) = \k h -> Dislike $ toQ p k h

type P s a = forall r. (Steps s r)  -> (Steps s (a :< r))
toP :: Parser s a -> P s a 
toP (Case a f) = \fut -> Sus (toP a fut) (\s -> toP (f s) fut)
toP (Appl f x) = App . toP f . toP x
toP (Pure x)   = Val x
toP Empt = \_fut -> Fail
toP (Disj a b)  = \fut -> iBest (toP a fut) (toP b fut)
toP (Bind p a2q) = \fut -> (toQ p) (\(_,a) -> (toP (a2q a)) fut) ()
toP (Yuck p) = Dislike . toP p 

iBest :: Steps s a -> Steps s a -> Steps s a
iBest p q = let ~(choice, pr) = better 0 (progress p) (progress q) in Best choice pr p q

-- parse p = fst $ evalR $ toP p (\_ -> Done) 

--------------------------------------------------
-- Extra stuff


instance Show (Steps s a) where
    show (Val _ p) = "v" ++ show p
    show (App p) = "*" ++ show p
    show (Done) = "1"
    show (Shift p) = ">" ++ show p
    show (Fail) = "0"
    show (Best _ _ p q) = "(" ++ show p ++ ")" ++ show q

-- | Pre-compute a left-prefix of some steps (as far as possible)
evalL :: Steps s a -> Steps s a
evalL (Shift p) = evalL p
evalL (Val x r) = Val x (evalL r)
evalL (App f) = case evalL f of
                  (Val a (Val b r)) -> Val (a b) r
                  r -> App r
evalL x@(Best choice _ p q) = case choice of
    LT -> evalL p
    GT -> evalL q
    EQ -> x -- don't know where to go: don't speculate on evaluating either branch.
evalL x = x

symbol f = Case empty $ \s -> if f s then pure s else empty
eof = Case (pure ()) (const empty)

parse p input = evalR $ push Nothing $ push (Just input) $ toP p Done

data Expr = V Int | Add Expr Expr
            deriving Show

type PP = Parser Char

sym x = symbol (== x)

pExprParen = symbol (== '(') *> pExprTop <* symbol (== ')')

pExprVal = V <$> toInt <$> symbol (isDigit)
    where toInt c = ord c - ord '0'

pExprAtom = pExprVal <|> pExprParen

pExprAdd = pExprAtom <|> Add <$> pExprAtom <*> (symbol (== '+') *> pExprAdd) 

pExprTop = pExprAdd

pExpr :: PP Expr
pExpr = pExprTop <* eof

syms [] = pure ()
syms (s:ss) = sym s *> syms ss

pTag  = sym '<' *> many (symbol (/= '>')) <* sym '>'
pTag' s = sym '<' *> syms s <* sym '>'

pTagged :: PP t -> PP t
pTagged p = do
    open <- pTag
    p <* pTag' open
    
p0 :: PP Int
p0 = (pure 1 <* sym 'a') <|> (pure 2)


p1 x = if x == 2 then sym 'a' *> pure 3 else sym 'b' *> pure 4

p2 :: PP Int
p2 = p0 >>= p1

test = parse (p0 >>= p1) "ab"

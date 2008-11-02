-- Copyright (c) JP Bernardy 2008
-- | This is a re-implementation of the "Polish Parsers" in a clearer way. (imho)
{-# OPTIONS -fglasgow-exts #-}
module SimplePolishPlusMonadInitial where

import Control.Applicative
import Data.List hiding (map, minimumBy)
import Data.Char
import Data.Maybe (listToMaybe)

data Parser s a where
    Bind :: Parser s a -> (a -> Parser s b) -> Parser s b
    Pure :: a -> Parser s a
    Appl :: Parser s (b -> a) -> Parser s b -> Parser s a
    Symb :: (s -> Bool) -> Parser s s
    Eof  :: Parser s ()
    Empt :: Parser s a
    Disj :: Parser s a -> Parser s a -> Parser s a

data Void
data a :< b -- o= (:<) {hd :: a, tl :: a}
infixr :<

data Steps s a where
    Val   :: a -> Steps s r               -> Steps s (a :< r)
    App   :: (Steps s ((b -> a) :< (b :< r)))      -> Steps s (a :< r)
    Done  ::                               Steps s Void
    Shift ::           Steps s a        -> Steps s a
    Fail ::                                Steps s a
    Best :: Ordering -> Progress -> Steps s a -> Steps s a -> Steps s a
    Susp :: Steps s a -> (s -> Steps s a) -> Steps s a

data Progress = PFail | PDone | PShift Progress
    deriving Show

better :: Progress -> Progress -> (Ordering, Progress)
better PFail p = (GT, p) -- avoid failure
better p PFail = (LT, p)
better p PDone = (GT, PDone)
better PDone p = (LT, PDone)
better (PShift p) (PShift q) = pstep (better p q)

pstep ~(ordering, xs) = (ordering, PShift xs)

progress :: Steps s a -> Progress
progress (Val _ p) = progress p
progress (App p) = progress p
progress (Shift p) = PShift (progress p)
progress (Done) = PDone
progress (Fail) = PFail
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



type P s a = forall r. Steps s r -> Steps s (a :< r)

type Q s a = forall h r. ((h,a) -> Steps s r) -> (h -> Steps s r)

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


toQ :: Parser s a -> Q s a
toQ (Symb f) = \fut h -> Susp 
      Fail -- This is the eof!
      $ \s -> if f s then Shift (fut (h, s))
                     else Fail
toQ (Eof) = \fut h -> Susp
      (Shift (fut (h, ())))
      (\_s -> Fail)
toQ (p `Appl` q) = \k -> toQ p $ toQ q $ \((h, b2a), b) -> k (h, b2a b)
toQ (Pure a)     = \k h -> k (h, a)
toQ (Disj p q)   = \k h -> iBest (toQ p k h) (toQ q k h)
toQ (Bind p a2q) = \fut -> (toQ p) (\(h,a) -> toQ (a2q a) fut h)
toQ Empt  = \k h -> Fail

toP :: Parser s a -> P s a 
toP (Symb f) = \fut -> Susp Fail $
      \s -> if f s then Shift (Val s fut)
                   else Fail
toP Eof = \fut -> Susp 
      (Shift (Val () fut))
      (\_s -> Fail)
toP (Appl f x) = App . toP f . toP x
toP (Pure x)   = Val x 
toP Empt = \_fut -> Fail
toP (Disj a b)  = \fut -> iBest (toP a fut) (toP b fut)
toP (Bind p a2q) = \fut -> (toQ p) (\(_,a) -> (toP (a2q a)) fut) ()

iBest :: Steps s a -> Steps s a -> Steps s a
iBest p q = let ~(choice, pr) = better (progress p) (progress q) in Best choice pr p q

parse p input = fst $ evalR $ push Nothing $ push (Just input) $ toP p Done

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
                  (Val f1 (App (Val f2 r))) -> App (Val (f1 . f2) r)
                  r -> App r
evalL x@(Best choice _ p q) = case choice of
    LT -> evalL p
    GT -> evalL q
    EQ -> x -- don't know where to go: don't speculate on evaluating either branch.
evalL x = x

push :: Maybe [s] -> Steps s a -> Steps s a
push (Just []) x = x

push ss (Val x s) = Val x (push ss s)
push ss (App f) = App (push ss f)
push ss (Best _ _ l r) = iBest (push ss l) (push ss r)
push ss Fail = Fail
push ss (Shift r) = Shift (push ss r)
push ss Done = Done
push (Just (s:ss)) (Susp nil cons) = push (Just ss) (cons s)
push (Nothing) (Susp nil cons) = push Nothing nil



------------------

data Expr = V Int | Add Expr Expr
            deriving Show

type PP = Parser Char

symbol = Symb

sym x = symbol (== x)

pExprParen = symbol (== '(') *> pExprTop <* symbol (== ')')

pExprVal = V <$> toInt <$> symbol (isDigit)
    where toInt c = ord c - ord '0'

pExprAtom = pExprVal <|> pExprParen

pExprAdd = pExprAtom <|> Add <$> pExprAtom <*> (symbol (== '+') *> pExprAdd) 

pExprTop = pExprAdd

pExpr :: PP Expr
pExpr = pExprTop <* Eof

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

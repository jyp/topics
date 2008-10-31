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

data Steps a where
    Val   :: a -> Steps r               -> Steps (a,r)
    App   :: (Steps (b -> a,(b,r)))      -> Steps (a,r)
    Done  ::                               Steps Void
    Shift ::           Steps a        -> Steps a
    Fail ::                                Steps a
    Best :: Ordering -> Progress -> Steps a -> Steps a -> Steps a

data Progress = PFail | PDone | PShift Progress
    deriving Show

better :: Progress -> Progress -> (Ordering, Progress)
better PFail p = (GT, p) -- avoid failure
better p PFail = (LT, p)
better p PDone = (GT, PDone)
better PDone p = (LT, PDone)
better (PShift p) (PShift q) = pstep (better p q)

pstep ~(ordering, xs) = (ordering, PShift xs)

progress :: Steps a -> Progress
progress (Val _ p) = progress p
progress (App p) = progress p
progress (Shift p) = PShift (progress p)
progress (Done) = PDone
progress (Fail) = PFail
progress (Best _ pr _ _) = pr

-- | Right-eval a fully defined process
evalR :: Steps (a,r) -> (a, Steps r)
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

type P s a = forall r. ([s] -> Steps r)  -> ([s] -> Steps (a,r))

type Q s a = forall h r. ((h,a) -> [s] -> Steps r)  -> (h -> [s] -> Steps r)

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
toQ (Symb f) = \fut h input -> case input of
      [] -> Fail -- This is the eof!
      (s:ss) -> if f s then Shift (fut (h, s) ss)
                       else Fail
toQ (Eof) = \fut h input -> case input of
      [] -> Shift (fut (h, ()) input)
      _ -> Fail
toQ (p `Appl` q) = \k -> toQ p $ toQ q $ \((h, b2a), b) -> k (h, b2a b)
toQ (Pure a)     = \k h input -> k (h, a) input
toQ (Disj p q)   = \k h input -> iBest (toQ p k h input) (toQ q k h input)
toQ (Bind p a2q) = \fut -> (toQ p) (\(h,a) i -> toQ (a2q a) fut h i)

toP :: Parser s a -> P s a 
toP (Symb f) = \fut input -> case input of
      [] -> Fail -- This is the eof!
      (s:ss) -> if f s then Shift (Val s (fut ss))
                       else Fail
toP Eof = \fut input -> case input of
      [] -> Shift (Val () $ fut input)
      _ -> Fail
toP (Appl f x) = (App .) . toP f . toP x
toP (Pure x)   = \fut input -> Val x $ fut input
toP Empt = \_fut _input -> Fail
toP (Disj a b)  = \fut input -> iBest (toP a fut input) (toP b fut input)
toP (Bind p a2q) = \fut -> (toQ p) (\(_,a) i -> (toP (a2q a)) fut i) ()

iBest :: Steps a -> Steps a -> Steps a
iBest p q = let ~(choice, pr) = better (progress p) (progress q) in Best choice pr p q

parse p input = fst $ evalR $ toP p (\_ -> Done) input

--------------------------------------------------
-- Extra stuff


instance Show (Steps a) where
    show (Val _ p) = "v" ++ show p
    show (App p) = "*" ++ show p
    show (Done) = "1"
    show (Shift p) = ">" ++ show p
    show (Fail) = "0"
    show (Best _ _ p q) = "(" ++ show p ++ ")" ++ show q

-- | Pre-compute a left-prefix of some steps (as far as possible)
evalL :: Steps a -> Steps a
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

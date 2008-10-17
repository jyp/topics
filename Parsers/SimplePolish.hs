-- Copyright (c) JP Bernardy 2008
-- | This is a re-implementation of the "Polish Parsers" in a clearer way. (imho)
{-# OPTIONS -fglasgow-exts #-}
module SimplePolish (Process, Void, 
                     symbol, eof, lookNext, runPolish, 
                     runP, progress, evalR,
                     P) where
import Control.Applicative
import Data.List hiding (map, minimumBy)
import Data.Char
import Data.Maybe (listToMaybe)

data Void

type Process a = Steps a (Steps Void Void)

data Steps a r where
    Val   :: a -> Steps b r               -> Steps a (Steps b r)
    App   :: Steps (b -> a) (Steps b r) -> Steps a r
    Done  ::                                   Steps Void Void
    Shift ::             Steps a r        -> Steps a r
    Fails ::                                   Steps a r
    Best :: Ordering -> Progress -> Steps a r -> Steps a r -> Steps a r

data Progress = PFail | PRes | Step Progress
    deriving Show

better :: Progress -> Progress -> (Ordering, Progress)
better PFail p = (GT, p) -- avoid failure
better p PFail = (LT, p)
better PRes PRes = (EQ, PRes)
better (Step p) (Step q) = pstep (better p q)

pstep ~(ordering, xs) = (ordering, Step xs)

progress :: Steps a r -> Progress
progress (Val _ p) = progress p
progress (App p) = progress p
progress (Shift p) = Step (progress p)
progress (Done) = PRes
progress (Fails) = PFail
progress (Best _ pr _ _) = pr

-- | Right-eval a fully defined process (ie. one that has no Suspend)
-- Returns value and continuation.
evalR :: Steps a r -> (a, r)
evalR z@(Val a r) = (a,r)
evalR (App s) = let (f, s') = evalR s
                    (x, s'') = evalR s'
                in (f x, s'')
evalR Done = error "evalR: Can't create values of type Void"
evalR (Shift v) = evalR v
evalR (Fails) = error "evalR: No parse!"
evalR (Best choice _ p q) = case choice of
    LT -> evalR p
    GT -> evalR q
    EQ -> error $ "evalR: Ambiguous parse: " ++ show p ++ " ~~~ " ++ show q

-- | A parser. (This is actually a parsing process segment)
newtype P s a = P (forall b r. ([s] -> Steps b r)  -> ([s] -> Steps a (Steps b r)))

instance Functor (P s) where
    fmap f x = pure f <*> x

instance Applicative (P s) where
    P f <*> P x = P ((App .) . f . x)
    pure x = P (\fut input -> Val x $ fut input)

instance Alternative (P s) where
    empty = P $ \_fut _input -> Fails
    P a <|> P b = P $ \fut input -> iBest (a fut input) (b fut input)
        where iBest p q = let ~(choice, pr) = better (progress p) (progress q) in Best choice pr p q

runP :: forall s a. P s a -> [s] -> Process a
runP (P p) input = p (\_input -> Done) input

-- | Run a parser.
runPolish :: forall s a. P s a -> [s] -> a
runPolish p input = fst $ evalR $ runP p input

-- | Parse a symbol
symbol :: (s -> Bool) -> P s s
symbol f = P $ \fut input -> case input of
    [] -> Fails -- This is the eof!
    (s:ss) -> if f s then Shift (Val s (fut ss))
                     else Fails

-- | Parse the eof
eof :: P s ()
eof = P $ \fut input -> case input of
    [] -> Shift (Val () $ fut input)
    _ -> Fails

--------------------------------------------------
-- Extra stuff


lookNext :: (Maybe s -> Bool) -> P s ()
lookNext f = P $ \fut input ->
   if (f $ listToMaybe input) then Val () (fut input)
                              else Fails
        

instance Show (Steps a r) where
    show (Val _ p) = "v" ++ show p
    show (App p) = "*" ++ show p
    show (Done) = "1"
    show (Shift p) = ">" ++ show p
    show (Fails) = "0"
    show (Best _ _ p q) = "(" ++ show p ++ ")" ++ show q

-- | Pre-compute a left-prefix of some steps (as far as possible)
evalL :: Steps a r -> Steps a r
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

pExprParen = symbol (== '(') *> pExprTop <* symbol (== ')')

pExprVal = V <$> toInt <$> symbol (isDigit)
    where toInt c = ord c - ord '0'

pExprAtom = pExprVal <|> pExprParen

pExprAdd = pExprAtom <|> Add <$> pExprAtom <*> (symbol (== '+') *> pExprAdd) 

pExprTop = pExprAdd

pExpr = pExprTop <* eof


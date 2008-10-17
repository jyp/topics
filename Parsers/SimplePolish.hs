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

data Steps a r where
    Val   :: a -> Steps b r             -> Steps a (Steps b r)
    App   :: Steps (b -> a) (Steps b r) -> Steps a r
    Done  ::                               Steps Void Void
    Shift ::           Steps a r        -> Steps a r
    Fail ::                                Steps a r
    Best :: Ordering -> Progress -> Steps a r -> Steps a r -> Steps a r

data Progress = PFail | PDone | PShift Progress
    deriving Show

better :: Progress -> Progress -> (Ordering, Progress)
better PFail p = (GT, p) -- avoid failure
better p PFail = (LT, p)
better PDone PDone = (EQ, PDone)
better (PShift p) (PShift q) = pstep (better p q)

pstep ~(ordering, xs) = (ordering, PShift xs)

progress :: Steps a r -> Progress
progress (Val _ p) = progress p
progress (App p) = progress p
progress (Shift p) = PShift (progress p)
progress (Done) = PDone
progress (Fail) = PFail
progress (Best _ pr _ _) = pr

-- | Right-eval a fully defined process
evalR :: Steps a r -> (a, r)
evalR z@(Val a r) = (a,r)
evalR (App s) = let (f, s') = evalR s
                    (x, s'') = evalR s'
                in (f x, s'')
evalR Done = error "evalR: there is no value of type Void"
evalR (Shift v) = evalR v
evalR (Fail) = error "evalR: No parse!"
evalR (Best choice _ p q) = case choice of
    LT -> evalR p
    GT -> evalR q
    EQ -> error $ "evalR: Ambiguous parse: " ++ show p ++ " ~~~ " ++ show q

-- | A parser. (This is actually a parsing process segment)
newtype P s a = P {fromP :: forall b r. ([s] -> Steps b r)  -> ([s] -> Steps a (Steps b r))}

-- | A complete process
type Process a = Steps a (Steps Void Void)

instance Functor (P s) where
    fmap f x = pure f <*> x

instance Applicative (P s) where
    P f <*> P x = P ((App .) . f . x)
    pure x = P (\fut input -> Val x $ fut input)

instance Alternative (P s) where
    empty = P $ \_fut _input -> Fail
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
    [] -> Fail -- This is the eof!
    (s:ss) -> if f s then Shift (Val s (fut ss))
                     else Fail

-- | Parse the eof
eof :: P s ()
eof = P $ \fut input -> case input of
    [] -> Shift (Val () $ fut input)
    _ -> Fail

------------------------
-- Monad interface


getVal :: Steps a (Steps b r) -> (a, Steps b r)
getVal (Val a s) = (a,s)
getVal (App   s) = let (f,s')  = getVal s
                       (a,s'') = getVal s' -- hugh, this will dig again in the same shit.
                   in (f a, s'')
getVal (Shift v) = let (a,r) = getVal v in (a,Shift r)
getVal (Fail)    = error "getVal: Fail!"
getVal (Best choice _ p q) = case choice of
    LT -> getVal p
    GT -> getVal q
    EQ -> error $ "getVal: Ambiguous parse: " ++ show p ++ " ~~~ " ++ show q


instance Monad (P s) where
    return = pure
    P p >>= q = P $ \fut input -> let (a,ps_qres) = getVal (p (fromP (q a) fut) input)
                                   in ps_qres
 -- This is from polish parsers, but I think is wrong!
 -- Indeed: 
 --  q depends on a;
 --  a depends on the result of p
 --  the result of p can be influenced by q,
 ---    indeed, q follows p, so if p has a disjunction, q will influence its result.

--------------------------------------------------
-- Extra stuff


lookNext :: (Maybe s -> Bool) -> P s ()
lookNext f = P $ \fut input ->
   if (f $ listToMaybe input) then Val () (fut input)
                              else Fail
        

instance Show (Steps a r) where
    show (Val _ p) = "v" ++ show p
    show (App p) = "*" ++ show p
    show (Done) = "1"
    show (Shift p) = ">" ++ show p
    show (Fail) = "0"
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


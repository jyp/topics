{-# OPTIONS -fglasgow-exts #-}
module Polish (Process, Void, 
                     symbol, eof, lookNext, runPolish, 
                     runP, evalR,
                     P) where
import Control.Applicative
import Data.List hiding (map, minimumBy)
import Data.Char
import Data.Maybe (listToMaybe)

data Void

data Steps a r where
    Val   :: a -> Steps b r             -> Steps a (Steps b r)
    App   :: Steps (b -> a) (Steps b r) -> Steps a r
    Shift ::           Steps a r        -> Steps a r
    Done ::            Steps a r        -> Steps a r
    Fail ::                                Steps a r

best :: Steps a r -> Steps a r -> Steps a r
Fail `best` p = p
q `best` Fail = q
Done _ `best` Done _ = error "ambiguous"
Done a `best` q = Done a
p `best` Done a = Done a
Shift v `best` Shift w = Shift (v `best` w)
p `best` q = getProgress id p `best` getProgress id q


-- | Advance in the result steps, pushing results in the continuation.
-- (Must return one of: Done, Shift, Fail)
getProgress :: (Steps a r -> Steps b t) -> Steps a r -> Steps b t
getProgress f (Val a s) = getProgress (f . Val a) s
getProgress f (App s)   = getProgress (f . App) s
getProgress f (Done p)  = Done (f p)
getProgress f (Shift p) = Shift (f p)
getProgress _ (Fail) = Fail

-- | Right-eval a fully defined process
evalR :: Steps a r -> (a, r)
evalR z@(Val a r) = (a,r)
evalR (App s) = let (f, s') = evalR s
                    (x, s'') = evalR s'
                in (f x, s'')
evalR (Done v) = evalR v
evalR (Shift v) = evalR v
evalR (Fail) = error "evalR: No parse!"

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
    P a <|> P b = P $ \fut input -> best (a fut input) (b fut input)

runP :: forall s a. P s a -> [s] -> Process a
runP (P p) input = p (\rest -> stop) input

stop = Done stop
void :: Void
void = error "no such thing as void"

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

instance Monad (P s) where
    return = pure
    P p >>= q = P $ \fut input -> let (a,ps_qres) = getVal (p (fromP (q a) fut) input)
                                   in ps_qres
 -- This is from polish parsers, but is ~w~r~o~n~g~!
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
    show (Done _) = "1"
    show (Shift p) = ">" ++ show p
    show (Fail) = "0"

-- | Pre-compute a left-prefix of some steps (as far as possible)
evalL :: Steps a r -> Steps a r
evalL (Shift p) = evalL p
evalL (Val x r) = Val x (evalL r)
evalL (App f) = case evalL f of
                  (Val a (Val b r)) -> Val (a b) r
                  (Val f1 (App (Val f2 r))) -> App (Val (f1 . f2) r)
                  r -> App r
evalL x = x


------------------

data Expr = V Int | Add Expr Expr
            deriving Show

sym x = symbol (== x)

pExprParen = symbol (== '(') *> pExprTop <* symbol (== ')')

pExprVal = V <$> toInt <$> symbol (isDigit)
    where toInt c = ord c - ord '0'

pExprAtom = pExprVal <|> pExprParen

pExprAdd = pExprAtom <|> Add <$> pExprAtom <*> (symbol (== '+') *> pExprAdd) 

pExprTop = pExprAdd

pExpr = pExprTop <* eof

syms [] = pure ()
syms (s:ss) = sym s *> syms ss

pTag  = sym '<' *> many (symbol (/= '>')) <* sym '>'
pTag' s = sym '<' *> syms s <* sym '>'

pTagged t p = do
    open <- pTag
    p <* pTag' open
    

p0 = (pure 1 <* sym 'a') <|> (pure 2)

p1 = \x -> if x == 2 then sym 'a' *> pure 3 else sym 'b' *> pure 4

test = runPolish (p0 >>= p1) "ab"
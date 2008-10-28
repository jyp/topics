-- Copyright (c) JP Bernardy 2008
-- | This is a re-implementation of the "Polish Parsers" in a clearer way. (imho)
{-# OPTIONS -fglasgow-exts #-}
module SimplePolishPlusMonad (Process, Void, Parser (..),
                     runP, progress, evalR,
                     P) where
import Control.Applicative
import Data.List hiding (map, minimumBy)
import Data.Char
import Data.Maybe (listToMaybe)

class Alternative (p s) => Parser p s where
    symbol :: (s -> Bool) -> p s s
    eof :: p s ()
    parse :: p s a -> [s] -> a

    

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
evalR z@(Val a r) = (a,r)
evalR (App s) = let (f, s') = evalR s
                    (x, s'') = evalR s'
                in (f x, s'')
evalR (Shift v) = evalR v
evalR (Fail) = error "evalR: No parse!"
evalR (Best choice _ p q) = case choice of
    LT -> evalR p
    GT -> evalR q
    EQ -> error $ "evalR: Ambiguous parse: " ++ show p ++ " ~~~ " ++ show q

-- | A parser. (This is actually a parsing process segment)
newtype P s a = P {fromP :: forall r. ([s] -> Steps r)  -> ([s] -> Steps (a,r))}
newtype Q s a = Q {fromQ :: forall h r. ((h,a) -> [s] -> Steps r)  -> (h -> [s] -> Steps r)}
data PQ s a = PQ {getQ :: Q s a, getP :: P s a}

instance Parser PQ s where
    eof = PQ eof eof
    symbol p = PQ (symbol p) (symbol p)
    parse (PQ q p) input = parse p input

instance Functor (PQ s) where
    fmap f ~(PQ p q) = PQ (fmap f p) (fmap f q)

instance Applicative (PQ s) where
    PQ hp fp <*> ~(PQ hq fq) = PQ (hp <*> hq) (fp <*> fq)
    pure a = PQ (pure a) (pure a)

instance Alternative (PQ s) where
    PQ hp fp <|> ~(PQ hq fq) = PQ (hp <|> hq) (fp <|> fq)
    empty = PQ empty empty
    
    

instance Monad (PQ s) where
    PQ (Q p) _ >>= a2q = PQ (Q $ \fut -> p (\(h,a) i -> fromQ (getQ (a2q a)) fut h i))
                            (P $ \fut -> p (\(_,a) i -> fromP (getP (a2q a)) fut i) ())
    return = pure

instance Parser Q s where
  -- | Parse a symbol
  symbol f = Q $ \fut h input -> case input of
      [] -> Fail -- This is the eof!
      (s:ss) -> if f s then Shift (fut (h, s) ss)
                       else Fail
  
  -- | Parse the eof
  eof = Q $ \fut h input -> case input of
      [] -> Shift (fut (h, ()) input)
      _ -> Fail

  parse (Q q) input = fst $ evalR $ q (\(h,a) input -> Val a Done) () input

instance Applicative (Q s) where
  (Q p) <*> (Q q)  =  Q (\k -> p $ q $ \((h, b2a), b) -> k (h, b2a b))
  pure a           =  Q (\k h input -> k (h, a) input)

instance Alternative (Q s) where
  (Q p) <|> (Q q)  = Q (\k h input -> iBest (p k h input) (q k h input)) 
  empty            = Q (\k _ _ -> Fail)

instance Functor (Q state) where
    f `fmap` (Q p)      =  Q  (\k -> p $ \(h, a) -> k (h, f a))

-- | A complete process
type Process a = Steps (a,Void)

instance Functor (P s) where
    fmap f x = pure f <*> x

instance Applicative (P s) where
    P f <*> P x = P ((App .) . f . x)
    pure x = P (\fut input -> Val x $ fut input)

instance Alternative (P s) where
    empty = P $ \_fut _input -> Fail
    P a <|> P b = P $ \fut input -> iBest (a fut input) (b fut input)

iBest :: Steps a -> Steps a -> Steps a
iBest p q = let ~(choice, pr) = better (progress p) (progress q) in Best choice pr p q

runP :: forall s a. P s a -> [s] -> Process a
runP (P p) input = p (\_input -> Done) input


instance Parser P s where
  -- | Parse a symbol
  symbol f = P $ \fut input -> case input of
      [] -> Fail -- This is the eof!
      (s:ss) -> if f s then Shift (Val s (fut ss))
                       else Fail
  
  -- | Parse the eof
  eof = P $ \fut input -> case input of
      [] -> Shift (Val () $ fut input)
      _ -> Fail

  -- | Run a parser.
  parse p input = fst $ evalR $ runP p input

--------------------------------------------------
-- Extra stuff


lookNext :: (Maybe s -> Bool) -> P s ()
lookNext f = P $ \fut input ->
   if (f $ listToMaybe input) then Val () (fut input)
                              else Fail
        

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

type PP = PQ Char

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

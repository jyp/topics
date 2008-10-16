-- Copyright (c) JP Bernardy 2008
{-# OPTIONS -fglasgow-exts #-}
module Yi.IncrementalParse (Process, Void, 
                            symbol, eof, lookNext, runPolish, 
                            runP, profile, evalR,
                            P, AlexState (..)) where
import Yi.Lexer.Alex (AlexState (..))
import Yi.Prelude
import Prelude (Ordering(..))
import Yi.Syntax
import Data.List hiding (map, minimumBy)
import Data.Char
import Data.Maybe (listToMaybe)

{- ----------------------------------------

- Based on a mix between "Polish Parsers, Step by Step (Hughes and Swierstra)", 
  and "Parallel Parsing Processes (Claessen)"
  
  It's strongly advised to read the papers! :)
- The parser has "online" behaviour.

  This is a big advantage because we don't have to parse the whole file to
  begin syntax highlight the beginning of it.

- Basic error correction

- Based on Applicative functors.

  This is not as powerful as Monadic parsers, but easier to work with. This is
  needed if we want to build the result lazily.


-------------------------------------------}



data Void

type Process s a = Steps s a (Steps s Void Void)


data Steps s a r where
    -- These constructors describe the tree of values, as above
    Val   :: a -> Steps s b r               -> Steps s a (Steps s b r)
    -- Doc: The process that returns the value of type @a@ which is followed by a parser returning a value of type @b@.
    App   :: Steps s (b -> a) (Steps s b r) -> Steps s a r
    -- Doc: Takes a process that returns a function @f@ of type @b -> a@ and is
    -- followed by a process returning a value @x@ of type @b@.  The resulting
    -- process will return the result of applying the function @f@ to @x@.
    Stop  ::                                   Steps s Void Void
 
    -- These constructors describe the parser state
    Shift ::             Steps s a r        -> Steps s a r
    Done  ::             Steps s a r        -> Steps s a r
    -- Doc: The parser that signals success.  The argument is the continuation.
    Fails ::                                   Steps s a r
    -- Doc: The parser that signals failure.

    Best :: Ordering -> Profile -> Steps s a r -> Steps s a r -> Steps s a r

data Profile = PFail | PRes | Step Profile
    deriving Show

better :: Profile -> Profile -> (Ordering, Profile)
better PFail p = (GT, p) -- avoid failure
better p PFail = (LT, p)
better PRes PRes = (LT, PRes) -- pick any 
better (Step p) (Step q) = pstep (better p q)

pstep ~(ordering, xs) = (ordering, Step xs)

profile :: Steps s a r -> Profile
profile (Val _ p) = profile p
profile (App p) = profile p
profile (Stop) = error "profile: Stop" -- this should always be "hidden" by Done
profile (Shift p) = Step (profile p)
profile (Done _) = PRes
profile (Fails) = PFail
profile (Best _ pr _ _) = pr


instance Show (Steps s a r) where
    show (Val _ p) = "v" ++ show p
    show (App p) = "*" ++ show p
    show (Stop) = "1"
    show (Shift p) = ">" ++ show p
    show (Done p) = "!" ++ show p
    show (Fails) = "0"
    show (Best _ _ p q) = "(" ++ show p ++ ")" ++ show q


-- | Right-eval a fully defined process (ie. one that has no Suspend)
-- Returns value and continuation.
evalR :: Steps s a r -> (a, r)
evalR z@(Val a r) = (a,r)
evalR (App s) = let (f, s') = evalR s
                    (x, s'') = evalR s'
                in (f x, s'')
evalR Stop = error "evalR: Can't create values of type Void"
evalR (Shift v) = evalR v
evalR (Done v)  = evalR v
evalR (Fails) = error "evalR: No parse!"
evalR (Best choice _ p q) = case choice of
    LT -> evalR p
    GT -> evalR q
    EQ -> error $ "evalR: Ambiguous parse: " ++ show p ++ " ~~~ " ++ show q

-- | Pre-compute a left-prefix of some steps (as far as possible)
evalL :: Steps s a r -> Steps s a r
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


-- | A parser. (This is actually a parsing process segment)
newtype P s a = P (forall b r. ([s] -> Steps s b r)  -> ([s] -> Steps s a (Steps s b r)))

instance Functor (P s) where
    fmap f x = pure f <*> x

instance Applicative (P s) where
    P f <*> P x = P ((App .) . f . x)
    pure x = P (\fut input -> Val x $ fut input)

instance Alternative (P s) where
    empty = P $ \_fut _input -> Fails
    P a <|> P b = P $ \fut input -> iBest (a fut input) (b fut input)

-- | Intelligent, caching best.
iBest p q = let ~(choice, pr) = better (profile p) (profile q) in Best choice pr p q


runP :: forall s a. P s a -> [s] -> Process s a
runP (P p) input = p (\_input -> Done Stop) input

-- | Run a parser.
runPolish :: forall s a. P s a -> [s] -> a
runPolish p input = fst $ evalR $ runP p input

-- | Parse a symbol
symbol :: (s -> Bool) -> P s s
symbol f = P $ \fut input ->
              case input of
                [] -> Fails -- This is the eof!
                (s:ss) -> if f s then Shift (Val s (fut ss))
                                 else Fails

lookNext :: (Maybe s -> Bool) -> P s ()
lookNext f = P $ \fut input ->
   if (f $ listToMaybe input) then Val () (fut input)
                              else Fails
        

-- | Parse the eof
eof :: P s ()
eof = P $ \fut input ->
              case input of
                [] -> Shift (Val () $ fut input)
                _ -> Fails



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


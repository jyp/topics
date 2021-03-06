{-# LANGUAGE EmptyDataDecls, ScopedTypeVariables #-}
-- Copyright (c) JP Bernardy 2008
module Yi.IncrementalParse (Process, Void, 
                            recoverWith, symbol, eof, runPolish,
                            P, AlexState (..), scanner) where
import Yi.Lexer.Alex (AlexState (..))
import Yi.Prelude
import Prelude ()
import Yi.Syntax
import Data.List hiding (map)

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

-- | Our parsing processes.
-- To understand the design of this data type it is important to consider the
-- basic design goal: Our parser should return a (partial) result as soon as
-- possible, that is, as soon as only one of all possible parses of an input
-- can succeed.  This also means we want to be able to return partial results.
-- We therefore have to transform our parse tree into a linearized form that
-- allows us to return parts of it as we parse them.  Consider the following
-- data type:
--
-- > data BinTree = Node BinTree BinTree | Leaf Int
-- > ex1 = Node (Leaf 1) (Node (Leaf 2) (Leaf 3))
--
-- Provided we know the arity of each constructor, we can unambiguously
-- represent @ex1@ (without using parentheses to resolve ambiguity) as:
--
-- > Node Leaf 1 Node Leaf 2 Leaf 3
--
-- This is simply a pre-order printing of the tree type and, in this case, is
-- exactly how we defined @ex1@ without all the parentheses.  It would,
-- however, be unnecessarily complicated to keep track of the arity of each
-- constructor, so we use a well-known trick: currying.  Note, that the
-- original definition of @ex1@ is actually a shorter notation for
--
-- > ((Node $ (Leaf $ 1)) $ ((Node $ (Leaf $ 2)) $ (Leaf $ 3)))
--
-- or as a tree
-- 
-- >                      $
-- >        .-------------'----------------------.
-- >        $                                    $
-- >     .--'-------.              .-------------'-------.
-- >   Node         $              $                     $
-- >             .--'-.         .--'-------.          .--'-.
-- >           Leaf   1       Node         $        Leaf   3
-- >                                    .--'-.
-- >                                  Leaf   2
--
-- where @$@ represents function application.  We can print this tree in
-- prefix-order:
--
-- > ($) ($) Node ($) Leaf 1 ($) ($) Node ($) Leaf 2 ($) Leaf 3
--
-- This consists of only two types of nodes -- values and applications -- but
-- we can construct values of any (non-strict) Haskell data type with it.
--
-- Unfortunately, it is a bit tricky to type those kinds of expressions in
-- Haskell.  [XXX: example; develop solution step by step; continuations]
--
-- The parameter @r@ represents the type of the remainder of our expression.

-- TODO: Replace 'Doc:' by ^ when haddock supports GADTs
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
    Dislike :: Steps s a r ->                                   Steps s a r

    Suspend :: ([s] -> Steps s a r) -> Steps s a r
    -- Doc: A suspension of the parser (this is the part borrowed from
    -- Parallel Parsing Processes) The parameter to suspend's
    -- continuation is a whole chunk of text; [] represents the
    -- end of the input
   

instance Show (Steps s a r) where
    show (Val _ p) = "v" ++ show p
    show (App p) = "*" ++ show p
    show (Stop) = "1"
    show (Shift p) = ">" ++ show p
    show (Done p) = "!" ++ show p
    show (Dislike p) = "?" ++ show p
    show (Fails) = "0"
    show (Suspend _) = "..."

-- data F a b where
--     Snoc :: F a b -> (b -> c) -> F a c
--     Nil  :: F a b
-- 
-- data S s a r where
--     S :: F a b -> Steps s a r -> S s a r


-- | Right-eval a fully defined process (ie. one that has no Suspend)
-- Returns value and continuation.
evalR :: Steps s a r -> (a, r)
evalR (Val a r) = (a,r)
evalR (App s) = let (f, s') = evalR s
                    (x, s'') = evalR s'
                in (f x, s'')
evalR Stop = error "evalR: Can't create values of type Void"
evalR (Shift v) = evalR v
evalR (Done v)  = evalR v
evalR (Dislike v) = -- trace "Yuck!" $ 
                    evalR v
evalR (Fails) = error "evalR: No parse!"
evalR (Suspend _) = error "evalR: Not fully evaluated!"


-- | Pre-compute a left-prefix of some steps (as far as possible)
evalL :: Steps s a r -> Steps s a r
evalL (Shift p) = evalL p
evalL (Dislike p) = evalL p
evalL (Val x r) = Val x (evalL r)
evalL (App f) = case evalL f of
                  (Val a (Val b r)) -> Val (a b) r
                  (Val f1 (App (Val f2 r))) -> App (Val (f1 . f2) r)
                  r -> App r
evalL x = x


-- | Push a chunk of symbols or eof in the process. This forces some suspensions.
push :: Maybe [s] -> Steps s a r -> Steps s a r
push (Just []) p = p  -- nothing more left to push
push ss p = case p of
                  (Suspend f) -> case ss of
                      Nothing -> f []
                      Just ss' -> f ss'
                  (Dislike p') -> Dislike (push ss p')
                  (Shift p') -> Shift (push ss p')
                  (Done p') -> Done (push ss p')
                  (Val x p') -> Val x (push ss p')
                  (App p') -> App (push ss p')
                  Stop -> Stop
                  Fails -> Fails

-- | Push some symbols.
pushSyms :: [s] -> Steps s a r -> Steps s a r
pushSyms x = push (Just x)

-- | Push eof
pushEof :: Steps s a r -> Steps s a r
pushEof = push Nothing

-- | A parser. (This is actually a parsing process segment)
newtype P s a = P (forall b r. Steps s b r -> Steps s a (Steps s b r))

instance Functor (P s) where
    fmap f x = pure f <*> x

instance Applicative (P s) where
    P f <*> P x = P (App . f . x)
    pure x = P (Val x)

instance Alternative (P s) where
    empty = P $ \_fut -> Fails
    P a <|> P b = P $ \fut -> best (a fut) (b fut)



-- | Advance in the result steps, pushing results in the continuation.
-- (Must return one of: Done, Shift, Fail)
getProgress :: (Steps s a r -> Steps s b t) -> Steps s a r -> Steps s b t
getProgress f (Val a s) = getProgress (f . Val a) s
getProgress f (App s)   = getProgress (f . App) s
-- getProgress f Stop   = f Stop
getProgress f (Done p)  = Done (f p)
getProgress f (Shift p) = Shift (f p)
getProgress f (Dislike p) = Dislike (f p)
getProgress _ (Fails) = Fails
getProgress _ Stop = error "getProgress: try to enter void"
getProgress f (Suspend p) = Suspend (\input -> f (p input))



best :: Steps x a s -> Steps x a s ->  Steps x a s
--l `best` r | trace ("best: "++show (l,r)) False = undefined
Suspend f `best` Suspend g = Suspend (\input -> f input `best` g input)

Fails   `best` p       = p
p `best` Fails         = p

Dislike a `best` b = bestD a b
a `best` Dislike b = bestD b a

Done a  `best` Done _  = Done a -- error "ambiguous grammar"
                                -- There are sometimes many ways to fix an error. Pick the 1st one.
Done a  `best` _       = Done a
_       `best` Done a  = Done a

Shift v `best` Shift w = Shift (v `best` w)

p       `best` q       = getProgress id p `best` getProgress id q


-- as best, but lhs is disliked.
bestD :: Steps x a s -> Steps x a s ->  Steps x a s

Suspend f `bestD` Suspend g = Suspend (\input -> f input `bestD` g input)

Fails   `bestD` p       = p
p `bestD` Fails         = Dislike p

a `bestD` Dislike b = Dislike (best a b)  -- back to equilibrium (prefer to do this, hence 1st case)
Dislike _ `bestD` b = b -- disliked twice: forget it.

Done _  `bestD` Done a  = Done a -- we prefer rhs in this case
Done a  `bestD` _       = Dislike (Done a)
_       `bestD` Done a  = Done a

Shift v `bestD` Shift w = Shift (v `bestD` w)
_       `bestD` Shift w = Shift w -- prefer shifting than keeping a disliked possibility forever


p       `bestD` q       = getProgress id p `bestD` getProgress id q



runP :: forall t t1.
                                    P t t1 -> Steps t t1 (Steps t Void Void)
runP (P p) = p (Done Stop)

-- | Run a parser.
runPolish :: forall s a. P s a -> [s] -> a
runPolish p input = fst $ evalR $ pushEof $ pushSyms input $ runP p

-- | Parse a symbol
symbol :: (s -> Bool) -> P s s
symbol f = P $ \fut -> Suspend $ \input ->
              case input of
                [] -> Fails -- This is the eof!
                (s:ss) -> if f s then push (Just ss) (Shift (Val s (fut)))
                                 else Fails

-- | Parse the eof
eof :: P s ()
eof = P $ \fut -> Suspend $ \input ->
              case input of
                [] -> Val () fut
                _ -> Fails

-- | Parse the same thing as the argument, but will be used only as
-- backup. ie, it will be used only if disjuncted with a failing
-- parser.
recoverWith :: forall s a. P s a -> P s a
recoverWith (P p) = P (Dislike . p)


----------------------------------------------------

type State st token result = (st, Process token result)

scanner :: forall st token result. P token result -> Scanner st token -> Scanner (State st token result) result
scanner parser input = Scanner 
    {
      scanInit = (scanInit input, runP parser),
      scanLooked = scanLooked input . fst,
      scanRun = run,
      scanEmpty = fst $ evalR $ pushEof $ runP parser
    }
    where
        run :: State st token result -> [(State st token result, result)]
        run (st,process) = updateState0 process $ scanRun input st

        updateState0 :: Process token result -> [(st,token)] -> [(State st token result, result)]
        updateState0 _        [] = []
        updateState0 curState toks@((st,tok):rest) = ((st, curState), result) : updateState0 nextState rest
            where nextState =       evalL $           pushSyms [tok]           $ curState
                  result    = fst $ evalR $ pushEof $ pushSyms (fmap snd toks) $ curState



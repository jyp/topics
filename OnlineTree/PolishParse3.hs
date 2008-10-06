{-# OPTIONS -fglasgow-exts #-}
module PolishParse3 (symbol', symbol, runP, eof, runPolish, recoverWith, push, evalL, evalR) where
import Debug.Trace (trace)
import Control.Applicative

data Void

data Steps s a r where
    Val   :: a -> Steps s b r               -> Steps s a (Steps s b r)
    App   :: Steps s (b -> a) (Steps s b r) -> Steps s a r
    Stop  ::                                   Steps s Void Void
    Shift ::             Steps s a r        -> Steps s a r
    Done  ::             Steps s a r        -> Steps s a r
    Fails ::                                   Steps s a r
    Dislike :: Steps s a r ->                                   Steps s a r
    Suspend :: (Maybe [s] -> Steps s a r) -> Steps s a r

instance Show (Steps s a r) where
    show (Val x p) = "v" ++ show p
    show (App p) = "*" ++ show p
    show (Stop) = "1"
    show (Shift p) = ">" ++ show p
    show (Done p) = "!" ++ show p
    show (Dislike p) = "?" ++ show p
    show (Fails) = "0"
    show (Suspend p) = "..."

-- data F a b where
--     Snoc :: F a b -> (b -> c) -> F a c
--     Nil  :: F a b
-- 
-- data S s a r where
--     S :: F a b -> Steps s a r -> S s a r

epicFail :: Steps s a r
epicFail = Fails


-- | Right-eval a fully defined process (ie. one that has no Suspend)
-- Returns value and continuation.
evalR :: Steps s a r -> (a, r)
evalR (Val a r) = (a,r)
evalR (App s) = let (f, s') = evalR s
                    (x, s'') = evalR s'
                in (f x, s'')
evalR Stop = error "Can't create values of type Void"
evalR (Shift v) = evalR v
evalR (Done v)  = evalR v
evalR (Dislike v) = -- trace "Yuck!" $ 
                    evalR v
evalR (Fails) = error "No parse!"
evalR (Suspend _) = error "Not fully evaluated!"


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


-- | Push a chunk of symbols or eof in the process. This force some suspensions.
push :: Maybe [s] -> Steps s a r -> Steps s a r
push ss p = case p of
                  (Suspend f) -> f ss
                  (Dislike p') -> Dislike (push ss p')
                  (Shift p') -> Shift (push ss p')
                  (Done p') -> Done (push ss p')
                  (Val x p') -> Val x (push ss p')
                  (App p') -> App (push ss p')
                  Stop -> Stop
                  Fails -> Fails


newtype P s a = P (forall b r. Steps s b r -> Steps s a (Steps s b r))

instance Functor (P s) where
    fmap f x = pure f <*> x

instance Applicative (P s) where
    P f <*> P x = P (App . f . x)
    pure x = P (Val x)

instance Alternative (P s) where
    empty = P $ \fut -> epicFail
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
getProgress f (Fails) = Fails
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
Done a  `best` q       = Done a
p       `best` Done a  = Done a

Shift v `best` Shift w = Shift (v `best` w)

p       `best` q       = getProgress id p `best` getProgress id q


-- as best, but lhs is disliked.
bestD :: Steps x a s -> Steps x a s ->  Steps x a s

Suspend f `bestD` Suspend g = Suspend (\input -> f input `bestD` g input)

Fails   `bestD` p       = p
p `bestD` Fails         = Dislike p

a `bestD` Dislike b = Dislike (best a b)  -- back to equilibrium (prefer to do this, hence 1st case)
Dislike a `bestD` b = b -- disliked twice: forget it.

Done _  `bestD` Done a  = Done a -- we prefer rhs in this case
Done a  `bestD` q       = Dislike (Done a)
p       `bestD` Done a  = Done a

Shift v `bestD` Shift w = Shift (v `bestD` w)
_       `bestD` Shift w = Shift w -- prefer shifting than keeping a disliked possibility forever


p       `bestD` q       = getProgress id p `bestD` getProgress id q




runP (P p) = p (Done Stop)


runPolish p input = fst $ evalR $ push Nothing $ push (Just input) $ runP p

symbol :: (s -> Bool) -> P s s
symbol f = P (\fut -> Suspend (symHelper fut))
    where symHelper fut input = 
              case input of
                Nothing -> epicFail -- This is the eof!
                Just [] ->  Suspend (symHelper fut) -- end of the chunk: to be continued
                Just (s:ss) -> if f s then push (Just ss) (Shift (Val s (fut)))
                               else epicFail

symbol' :: Eq s => s -> P s s
symbol' s0 = P (\fut -> Suspend (symHelper fut))
    where symHelper fut input = 
              case input of
                Nothing -> Dislike $ Shift $ Val s0 $ fut -- This is the eof!
                Just [] ->  Suspend (symHelper fut) -- end of the chunk: to be continued
                Just (s:ss) -> if s0 == s then push (Just ss) (Shift (Val s (fut)))
                               else  push (Just ss) $ Dislike $ Shift $ Val s0 $ fut 


eof :: P s ()
eof = P (\fut -> Suspend (symHelper fut))
    where symHelper fut input = 
              case input of
                Nothing -> Val () fut
                Just [] ->  Suspend (symHelper fut) -- end of the chunk: to be continued
                Just (s:ss) -> epicFail


-- eof = P $ \fut input -> 
--      case input of
--        Just (x:xs) -> epicFail
--        Nothing -> Val () fut

recoverWith (P p) = P (Dislike . p)

-- check f p = p <*> (\x -> if f x then pure x else empty)


x = 3 + 4
{-# OPTIONS -fglasgow-exts #-}
module Code(
            -- * Parser construction
            Parser(..),
            -- * Working with parsing processes
            mkProcess,
            evalZR,
            evalZL,
            feedSyms,
            -- * Debug
            runParser
           ) where

-- * Parser Interface

-- Parser specification
data Parser s a where
    Pure   :: a                               ->  Parser s a
    (:*:)  :: Parser s (b -> a) -> Parser s b ->  Parser s a
    Symb   :: Parser s a -> (s -> Parser s a) ->  Parser s a
    (:|:)  :: Parser s a -> Parser s a        ->  Parser s a
    Yuck   :: Parser s a                      ->  Parser s a

-- Running interface
--- interface 

mkProcess :: Parser s a -> Zip s (a :< Nil)
mkProcess p = Zip RStop (toP p $ Done)

feedSyms :: Maybe [s] -> Zip s t -> Zip s t
feedSyms syms (Zip l r) = evalZL (Zip l (feed syms r))

evalZR :: Zip token (a :< rest) -> a
evalZR (Zip l r) = top (evalRP l (evalR r))

-- Stacks
data top :< rest = (:<) {top :: top, rest :: rest}
infixr :<
data Nil = Nil

-- Polish + Progress
data Polish s a where
    Push    :: a -> Polish s r                      -> Polish s (a :< r)
    App     :: Polish s ((b -> a) :< (b :< r))      -> Polish s (a :< r)
    Done    ::                               Polish s Nil
    Shift   ::           Polish s a        -> Polish s a
    Sus     :: Polish s a -> (s -> Polish s a) -> Polish s a
    Best    :: Ordering -> Progress -> Polish s a -> Polish s a -> Polish s a
    Dislike :: Polish s a -> Polish s a

-- From Parsers to Polish
type P s a = forall r. (Polish s r) -> (Polish s (a :< r))
toP :: Parser s a -> P s a 
toP (Symb a f) = \fut -> Sus (toP a fut) (\s -> toP (f s) fut)
toP (f :*: x) = App . toP f . toP x
toP (Pure x)   = Push x
toP ((:|:) a b)  = \fut -> mkBest (toP a fut) (toP b fut)
toP (Yuck p) = Dislike . toP p 

-- Working with polish representation
feed :: Maybe [s] -> Polish s r -> Polish s r
feed (Just []) p = p  -- nothing more left to feed
feed ss p = case p of
                  (Sus nil cons) ->Shift $ case ss of
                      Nothing -> feed ss nil
                      Just [] -> p
                      Just (s:ss') -> feed (Just ss') (cons s)
                  (Dislike p') -> Dislike (feed ss p')
                  (Shift p') -> Shift (feed ss p')
                  (Push x p') -> Push x (feed ss p')
                  (App p') -> App (feed ss p')
                  Done -> Done
                  Best _ _ p' q' -> mkBest (feed ss p') (feed ss q')


-- Handling disjunction and errors.
data Progress = PSusp | PRes Int | !Int :> Progress
    deriving Show

mapSucc PSusp = PSusp
mapSucc (PRes x) = PRes (succ x) 
mapSucc (x :> xs) = succ x :> mapSucc xs

dislikeThreshold _ = 0

-- Compute the combination of two profiles, as well as which one is the best.
better :: Int -> Progress -> Progress -> (Ordering, Progress)
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

progress :: Polish s r -> Progress
progress (Push _ p) = progress p
progress (App p) = progress p
progress (Shift p) = 0 :> progress p
progress (Done) = PRes 0 -- success with zero dislikes
progress (Dislike p) = mapSucc (progress p)
progress (Sus _ _) = PSusp
progress (Best _ pr _ _) = pr

mkBest :: Polish s a -> Polish s a -> Polish s a
mkBest p q = let ~(choice, pr) = better 0 (progress p) (progress q) in Best choice pr p q

------------------------------------
-- Feeding symbols into the process

-----------------------
-- By-value evaluation
data RPolish input output where
  RPush :: a -> RPolish (a :< rest) output -> RPolish rest output
  RApp :: RPolish (b :< rest) output -> RPolish ((a -> b) :< a :< rest) output 
  RStop :: RPolish rest rest


-- Evaluate the output of an RPolish automaton, given an input stack
evalRP :: RPolish input output -> input -> output
evalRP RStop  acc = acc
evalRP (RPush v r) acc = evalRP r (v :< acc)
evalRP (RApp r) ~(f :< ~(a :< rest)) = evalRP r (f a :< rest)


-- Gluing a Polish expression and an RP automaton.
-- This can also be seen as a zipper of Polish expressions.
data Zip s output where
   Zip :: RPolish mid output -> Polish s mid -> Zip s output
   -- note that the Stack produced by the Polish expression matches
   -- the stack consumed by the RP automaton.

-- Move the zipper to the right, if possible.  The type gives evidence
-- that this function does not change the (type of) output produced.
right :: Zip s output -> Zip s output
right (Zip l (Push a r)) = Zip (RPush a l) r
right (Zip l (App r)) = Zip (RApp l) r
right (Zip l s) = (Zip l s)

onLeft :: (forall i o. RPolish i o -> RPolish i o) -> Zip s a -> Zip s a
onLeft f (Zip x y) = (Zip (f x) y)



evalR :: Polish s r -> r
evalR Done = Nil
evalR (Push a r) = a :< evalR r
evalR (App s) = apply (evalR s)
  where apply ~(f:< ~(a:<r)) = f a :< r
evalR (Shift v) = evalR v
evalR (Dislike v) = (evalR v)
evalR (Sus _ _) = error "evalR: Not fully evaluated!"
evalR (Best choice _ p q) = case choice of
    LT -> evalR p
    GT -> evalR q
    EQ -> error $ "evalR: Ambiguous parse: " ++ show p ++ " ~~~ " ++ show q

evalZL :: Zip s output -> Zip s output
evalZL (Zip l (Push a r)) = evalZL (Zip (simplify (RPush a l)) r)
evalZL (Zip l (App r)) = evalZL (Zip (RApp l) r)
evalZL (Zip l (Shift p)) = evalZL (Zip l p)
evalZL (Zip l (Dislike p)) = evalZL (Zip l p)
evalZL (Zip l r@(Best choice _ p q)) = case choice of
              LT -> evalZL (Zip l p)
              GT -> evalZL (Zip l q)
              EQ -> Zip l r -- don't know where to go: don't speculate on evaluating either branch.
evalZL (Zip l r) = Zip l r -- done or susp

----------------------------------------
-- Extra functions for explanation

-------------
evalA :: Parser s a -> a
evalA (f :*: x) = (evalA f) (evalA x)
evalA (Pure x) = x


-- The expression `(+ 2 3)` in direct, applicative and polish style.
-- expr = S [Atom 'a']
-- expr0 = S ((:) (Atom 'a') [])
-- expr' = Pure S :*: (Pure (:) :*: (Pure Atom :*: Pure 'a') :*: Pure [])
-- expr'' = App $ Push S $ App $ App $ Push (:) $ App $ Push Atom $ Push 'a' $ Push [] $ Done
-- 
-- suff = Push (:) $ App $ Push Atom $ Push 'a' $ Push [] $ Done

-- execute the automaton as far as possible
simplify :: RPolish s output -> RPolish s output
simplify (RPush a (RPush f (RApp r))) = simplify (RPush (f a) r)
simplify x = x

-- | Eval in both directions
evalX :: Zip s output -> Polish s r -> (r, [Zip s output])
evalX z s0 = case s0 of
    Push a r -> m (a :<)  (evalX z' r)
    App s -> m apply (evalX z' s)
   where z' = onLeft simplify (right z)
         m f ~(s, zz) = z' `seq` (f s, z':zz) -- tie the evaluation of the intermediate stuffs

apply ~(f:< ~(a:<r)) = f a :< r

---------------
-- Debug

instance Show (Zip s o) where
    show (Zip l r) = show l ++ show r

instance Show (Polish s r) where
    show (Push _ p) = "v" ++ show p
    show (App p) = "*" ++ show p
    show (Done) = "1"
    show (Shift p) = ">" ++ show p
    show (Dislike p) = "?"  ++ show p
    show (Sus _ _) = "..."
    show (Best _ _ p q) = "(" ++ show p ++ ")" ++ show q

instance Show (RPolish i o) where
    show (RPush _ p) = show p ++ "^"
    show (RApp p) = show p ++ "@"
    show (RStop) = "!"



runParser :: Parser s a -> [s] -> a
runParser p i = top $ evalR $ feed Nothing $ feed (Just i)  $ toP p $ Done

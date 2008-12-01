{-# OPTIONS -fglasgow-exts #-}
module FullIncrParser where

data a :< b

-- Parser specification
data Parser s a where
    Pure :: a -> Parser s a
    (:@:) :: Parser s (b -> a) -> Parser s b -> Parser s a
    Case :: Parser s a -> (s -> Parser s a) -> Parser s a
    Empt :: Parser s a
    Disj :: Parser s a -> Parser s a -> Parser s a
    Yuck :: Parser s a -> Parser s a


data Steps s a where
    Push   :: a -> Steps s r                      -> Steps s (a :< r)
    App   :: Steps s ((b -> a) :< (b :< r))      -> Steps s (a :< r)
    Done  ::                               Steps s ()
    Shift ::           Steps s a        -> Steps s a
    Fail ::                                Steps s a
    Sus :: Steps s a -> (s -> Steps s a) -> Steps s a
    Best :: Ordering -> Progress -> Steps s a -> Steps s a -> Steps s a
    Dislike :: Steps s a -> Steps s a

feed :: Maybe [s] -> Steps s r -> Steps s r
feed (Just []) p = p  -- nothing more left to feed
feed ss p = case p of
                  (Sus nil cons) -> case ss of
                      Nothing -> feed ss nil
                      Just [] -> p
                      Just (s:ss') -> feed (Just ss') (cons s)
                  (Dislike p') -> Dislike (feed ss p')
                  (Shift p') -> Shift (feed ss p')
                  (Push x p') -> Push x (feed ss p')
                  (App p') -> App (feed ss p')
                  Done -> Done
                  Fail -> Fail
                  Best _ _ p' q' -> iBest (feed ss p') (feed ss q')

data Progress = PSusp | PFail | PRes Int | !Int :> Progress
    deriving Show

mapSucc PSusp = PSusp
mapSucc PFail = PFail
mapSucc (PRes x) = PRes (succ x) 
mapSucc (x :> xs) = succ x :> mapSucc xs

dislikeThreshold _ = 0

-- Compute the combination of two profiles, as well as which one is the best.
better :: Int -> Progress -> Progress -> (Ordering, Progress)
better _ PFail p = (GT, p) -- avoid failure
better _ p PFail = (LT, p)
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

progress :: Steps s r -> Progress
progress (Push _ p) = progress p
progress (App p) = progress p
progress (Shift p) = 0 :> progress p
progress (Done) = PRes 0 -- success with zero dislikes
progress (Fail) = PFail
progress (Dislike p) = mapSucc (progress p)
progress (Sus _ _) = PSusp
progress (Best _ pr _ _) = pr

-- Right-eval a fully defined process
evalR :: Steps s (a :< r) -> (a, Steps s r)
evalR (Push a r) = (a,r)
evalR (App s) = let (f, s') = evalR s
                    (x, s'') = evalR s'
                in (f x, s'')
evalR (Shift v) = evalR v
evalR (Fail) = error "evalR: No parse!"
evalR (Dislike p) = evalR p
evalR (Best choice _ p q) = case choice of
    LT -> evalR p
    GT -> evalR q
    EQ -> error $ "evalR: Ambiguous parse!"

type P s a = forall r. (Steps s r) -> (Steps s (a :< r))
toP :: Parser s a -> P s a 
toP (Case a f) = \fut -> Sus (toP a fut) (\s -> toP (f s) fut)
toP (f :@: x) = App . toP f . toP x
toP (Pure x)   = Push x
toP Empt = \_fut -> Fail
toP (Disj a b)  = \fut -> iBest (toP a fut) (toP b fut)
toP (Yuck p) = Dislike . toP p 

iBest :: Steps s a -> Steps s a -> Steps s a
iBest p q = let ~(choice, pr) = better 0 (progress p) (progress q) in Best choice pr p q

symbol f = Case Empt $ \s -> if f s then Pure s else Empt
eof f = Case (Pure ()) (const Empt)
--------------------------------
-- The zipper for efficient evaluation:

-- Arbitrary expressions in Reverse Polish notation.
-- This can also be seen as an automaton that transforms a stack.
-- RPolish is indexed by the types in the stack consumed by the automaton (input),
-- and the stack produced (output)
data RPolish input output where
  RPush :: a -> RPolish (a :< rest) output -> RPolish rest output
  RApp :: RPolish (b :< rest) output -> RPolish ((a -> b) :< a :< rest) output 
  RStop :: RPolish rest rest

-- Evaluate the output of an RP automaton, given an input stack
evalRP :: RPolish input output -> input -> output
evalRP RStop acc = acc 
evalRP (RPush v r) acc = evalRP r (v :< acc)
evalRP (RApp r) (f :< a :< acc) = evalRP r (f a :< acc)


-- execute the automaton as far as possible
simplify :: RPolish s output -> RPolish s output
simplify (RPush a (RPush f (RApp r))) = simplify (RPush (f a) r)
simplify x = x

-- Gluing a Polish expression and an RP automaton.
-- This can also be seen as a zipper of Polish expressions.
data Zip output where
   Zip :: RPolish stack output -> Steps stack -> Zip output
   -- note that the Stack produced by the Polish expression matches
   -- the stack consumed by the RP automaton.

-- Move the zipper to the right, if possible.  The type gives evidence
-- that this function does not change the (type of) output produced.
right :: Zip output -> Zip output
right (Zip l (Val a r)) = Zip (RPush a l) r
right (Zip l (App r)) = Zip (RApp l) r
right (Zip l s) = (Zip l s)

-- | Pre-compute a left-prefix of some steps (as far as possible)
evalZL :: Zip output -> Zip output
evalZL z = case right z of
    Zip l r -> Zip (simplify l) r

--------------------------------

data SExpr = S [SExpr] | Atom Char

showL d = concatMap (showS (d+1))

showS d (Atom c) = [c]
showS d (S s) = open : showL d s ++ [close]
    where [open,close] = pp !! (d `mod` length pp) 
          pp = ["()","[]","{}"]

runParser :: Parser s a -> [s] -> a
runParser p i = fst $ evalR $ feed Nothing $ feed (Just i)  $ toP p $ Done

parseList :: Parser Char [SExpr]
parseList = Case 
   (Pure [])
   (\c -> case c of
       ')' -> Pure []
       '(' -> Pure (\arg rest -> S arg : rest ) :@: parseList :@: parseList
       c -> Pure (Atom c :) :@:  parseList)


-- The expression `(+ 2 3)` in direct, applicative and polish style.
expr = S [Atom 'a']
expr = S ((:) (Atom 'a') [])
expr' = Pure S :@: (Pure (:) :@: (Pure Atom :@: Pure 'a') :@: Pure [])
expr'' = App $ Push S $ App $ App $ Push (:) $ App $ Push Atom $ Push 'a' $ Push []



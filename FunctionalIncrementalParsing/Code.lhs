
\begin{code}

{-# OPTIONS -fglasgow-exts #-}
module Code(
            -- * Parser construction
            Parser(..),
            -- * Working with parsing processes
            Process,
            runParser, -- direct run
            mkProcess,
            finish,
            precompute,
            feedEof, feed) where

-- Parser specification
data Parser s a where
    Pure   :: a                                ->  Parser s a
    (:*:)  :: Parser s (b -> a) -> Parser s b  ->  Parser s a
    Symb   :: Parser s a -> (s -> Parser s a)  ->  Parser s a
    Disj   :: Parser s a -> Parser s a         ->  Parser s a
    Yuck   :: Parser s a                       ->  Parser s a

-- Working with parsing processes
type Process s a = Zip s (a :< Nil)

runParser :: Parser s a -> [s] -> a
runParser p i = finish $ feedEof $ feed i $ mkProcess p

mkProcess :: Parser s a -> Zip s (a :< Nil)
mkProcess p = Zip RStop (toP p $ Done)

feedSyms :: Maybe [s] -> Zip s t -> Zip s t
feedSyms syms (Zip l r) = Zip l (feed0 syms r)

feedEof = feedSyms Nothing
feed = feedSyms . Just

finish :: Zip token (a :< rest) -> a
finish (Zip l r) = top (evalRP l (evalR r))

-- Stacks
data top :< rest = (:<) {top :: top, rest :: rest}
infixr :<
data Nil = Nil


-- Polish + Progress
data Polish s a where
    Push     ::  a -> Polish s r                      ->  Polish s (a :< r)
    App      ::  Polish s ((b -> a) :< b :< r)
                                                      ->  Polish s (a :< r)
    Done     ::                                           Polish s Nil
    Shift    ::  Polish s a                           ->  Polish s a
    Susp     ::  Polish s a -> (s -> Polish s a) 
                                                      ->  Polish s a
    Best     ::  Ordering -> Progress -> 
                 Polish s a -> Polish s a             ->  Polish s a
    Dislike  ::  Polish s a                           ->  Polish s a

toP :: Parser s a -> (Polish s r -> Polish s (a :< r))
toP (Symb a f)  = \fut -> Susp (toP a fut)
                               (\s -> toP (f s) fut)
toP (f :*: x)   = App . toP f . toP x
toP (Pure x)    = Push x
toP (Disj a b)  = \fut -> mkBest (toP a fut) (toP b fut)
toP (Yuck p)    = Dislike . toP p 

-- Working with polish representation

-- feed some symbols into the process. 
-- |Nothing| represents the end of file.
feed0 :: Maybe [s] -> Polish s r -> Polish s r
feed0 (Just []) p = p  -- nothing more left to feed0
feed0 ss p = case p of
                  (Susp nil cons) ->Shift $ case ss of
                      Nothing -> feed0 ss nil
                      Just [] -> p
                      Just (s:ss') -> feed0 (Just ss') (cons s)
                  (Dislike p') -> Dislike (feed0 ss p')
                  (Shift p') -> Shift (feed0 ss p')
                  (Push x p') -> Push x (feed0 ss p')
                  (App p') -> App (feed0 ss p')
                  Done -> Done
                  Best _ _ p' q' -> mkBest (feed0 ss p') (feed0 ss q')


-- Handling disjunction and errors.
data Progress = PSusp | PRes Int | Int :> Progress
    deriving Show

mapSucc PSusp = PSusp
mapSucc (PRes x) = PRes (succ x) 
mapSucc (x :> xs) = succ x :> mapSucc xs

dislikeThreshold _ = 0

-- Compute the combination of two profiles, 
-- as well as which one is the best.
better _ PSusp _ = (EQ, PSusp)
better _ _ PSusp = (EQ, PSusp)
better _ (PRes x) (PRes y) = 
   if x <= y then (LT, PRes x) else (GT, PRes y)
better lk xs@(PRes x) (y:>ys) = 
   if x == 0 || y-x > dislikeThreshold lk 
   then (LT, xs) 
   else min x y +> better (lk+1) xs ys
better lk (y:>ys) xs@(PRes x) = 
   if x == 0 || y-x > dislikeThreshold lk 
   then (GT, xs) 
   else min x y +> better (lk+1) ys xs
better lk (x:>xs) (y:>ys)
    | x == 0 && y == 0 = rec
    | y - x > threshold = (LT, x:>xs)
    | x - y > threshold = (GT, y:>ys)
    | otherwise = rec
    where  threshold = dislikeThreshold lk
           rec = min x y +> better (lk + 1) xs ys
x +> ~(ordering, xs) = (ordering, x :> xs)

progress :: Polish s r -> Progress
progress (Push _ p)       = progress p                          
progress (App p)          = progress p                          
progress (Shift p)        = 0 :> progress p
progress (Done)           = PRes 0
progress (Dislike p)      = mapSucc (progress p)                
progress (Susp _ _)        = PSusp                               
progress (Best _ pr _ _)  = pr                                  

mkBest :: Polish s a -> Polish s a -> Polish s a
mkBest p q = 
   let  (choice, pr) = better 0 (progress p) (progress q) 
   in   Best choice pr p q



-- Reverse polish
data RPolish inp out where
  RPush  :: a -> RPolish (a :< r) out ->
               RPolish r out
  RApp   :: RPolish (b :< r) out ->
               RPolish ((a -> b) :< a :< r) out 
  RStop  ::    RPolish r r

-- Evaluate the output of an RPolish automaton, given an input stack
evalRP :: RPolish inp out -> inp -> out
evalRP RStop acc          = acc 
evalRP (RPush v r) acc    = evalRP r (v :< acc)
evalRP (RApp r) ~(f :< ~(a :< acc)) 
                          = evalRP r (f a :< acc)

-- Gluing a Polish expression and an RP automaton.
-- This can also be seen as a zipper of Polish expressions.
data Zip s output where
   Zip :: RPolish mid output -> Polish s mid -> Zip s output
   -- note that the Stack produced by the Polish expression matches
   -- the stack consumed by the RP automaton.

precompute :: Zip s output -> Zip s output
precompute (Zip l (Push a r))            =  precompute (Zip (simplify (RPush a l)) r)
precompute (Zip l (App r))               =  precompute (Zip (RApp l) r)              
precompute (Zip l (Shift p))             =  precompute (Zip l p)                     
precompute (Zip l (Dislike p))           =  precompute (Zip l p)                     
precompute (Zip l r@(Best choice _ p q)) =  case choice of                       
              LT ->  precompute (Zip l p) 
              GT ->  precompute (Zip l q) 
              EQ ->  Zip l r  
precompute (Zip l r)                     =  Zip l r

-- execute the automaton as far as possible
simplify :: RPolish s output -> RPolish s output
simplify (RPush a (RPush f (RApp r))) = simplify (RPush (f a) r)
simplify x = x


evalR :: Polish s r -> r
evalR Done                   = Nil                                
evalR (Push a r)             = a :< evalR r                       
evalR (App s)                = apply (evalR s)                    
  where apply ~(f:< ~(a:<r)) = f a :< r                           
evalR (Shift v)              = evalR v                            
evalR (Dislike v)            = (evalR v)                          
evalR (Susp _ _)              = error "input pending"
evalR (Best choice _ p q)    = case choice of                     
    LT -> evalR p
    GT -> evalR q
    EQ -> error $ "evalR: Ambiguous parse!"

\end{code}

\ignore{

----------------------------------------
-- Extra functions for explanation


-- Move the zipper to the right, if possible.  The type gives evidence
-- that this function does not change the (type of) output produced.
right :: Zip s output -> Zip s output
right (Zip l (Push a r)) = Zip (RPush a l) r
right (Zip l (App r)) = Zip (RApp l) r
right (Zip l s) = (Zip l s)

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


-- Eval in both directions
evalX :: Zip s output -> Polish s r -> (r, [Zip s output])
evalX z s0 = case s0 of
    Push a r -> m (a :<)  (evalX z' r)
    App s -> m apply (evalX z' s)
   where z' = onLeft simplify (right z)
         m f ~(s, zz) = z' `seq` (f s, z':zz) -- tie the evaluation of the intermediate stuffs

apply ~(f:< ~(a:<r)) = f a :< r


onLeft :: (forall i o. RPolish i o -> RPolish i o) -> Zip s a -> Zip s a
onLeft f (Zip x y) = (Zip (f x) y)



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
    show (RApp p) = show p ++ "a"
    show (RStop) = "!"

⟩


}





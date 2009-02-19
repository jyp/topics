{-# LANGUAGE GADTs, TypeOperators #-}

-- | This is a type "higher order" abstract machines with abitrary Haskell constants.
-- Everything is fully typed.

-- The cool thing is that the evaluator can go further than whnf.
-- This is important because the Haskell "environment" is interested in the fully evaluated
-- value in the end. We can also finely control how much we want to evaluate.

import Control.Applicative

data a :< b = (:<) {top :: a, _rest :: b}
infixr :<


data Term a where
     Lam :: (Term a -> Term b) -> Term (a -> b)
     App :: Term (a -> b) -> Term a -> Term b
     Con :: a -> Term a


instance Functor Term where
     fmap f = (pure f <*>)

instance Applicative Term where
   pure = Con
   (<*>) = App


ex1 = Lam $ \a -> Lam $ \b -> Con (+) `App` a `App` b

----------------------------
-- Direct evaluation

eval :: Term t -> t
eval (App t1 t2) = eval t1 (eval t2)
eval (Lam f) = \x -> eval (f (Con x))
eval (Con x) = x

instance Monad Term where
    return = Con
    k >>= f = f (eval k)


---------------------------
-- Call by name machinery

data RPolish input output where
  RPush :: a -> RPolish (a :< rest) output -> RPolish rest output
  RAppp :: RPolish (b :< rest) output -> RPolish ((a -> b) :< a :< rest) output 
  RStop :: RPolish rest rest

data Polish a where
    Push   :: Term a -> Polish r                      -> Polish (a :< r)
    Appp   :: Polish ((b -> a) :< (b :< r))      -> Polish (a :< r)
    Stop  ::                               Polish ()

data State output where
  State :: RPolish s output ->Polish s -> State output

-- Try to perform one step of evaluation.
stp :: State t -> State t
stp (State l         Stop)                              = (State l Stop)                        
stp (State l         (Appp r))                          = State (RAppp l)   r
stp (State l         (Push (App t1 t2) r))              = State l           (Appp (Push t1 (Push t2 r)))  
stp (State (RAppp l) (Push (Lam f) (Push a r)))         = State l           (Push (f a) r)                
stp (State l         (Push (Con x) r))                  = State (RPush x l) r -- TODO: simplify!

-- Unmatched:
--                      State RStop (Push (Lam _) _)
--                      State (RPush _ _) (Push (Lam _) _)

--                      State (RAppp _) (Push (Lam _) Stop)


--                      State (RAppp _) (Push (Lam _) (Appp _))

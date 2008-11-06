{-# LANGUAGE GADTs #-}

import Control.Applicative


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

data State output where
   State :: Term fct -> Stack fct output -> State output

data Stack fct output where
    Nil :: Stack output output
    Cons :: Term a -> Stack fct output -> Stack (a -> fct) output

step :: State t -> State t
step (State (App t1 t2) s)      = State t1 (Cons t2 s)
step (State (Lam f) (Cons a s)) = State (f a) s


cbnExec :: State t -> t
cbnExec (State (App t1 t2) s)      = cbnExec (State t1 (Cons t2 s))
cbnExec (State (Lam f) (Cons a s)) = cbnExec (State (f a) s)
cbnExec (State (Lam f) Nil) = \x -> cbnExec (State (f (Con x)) Nil)
-- this is a rule that cannot be in the untyped version.
cbnExec (State (Con x) s) = app x s

app :: fct -> Stack fct output -> output
app x s = case s of
    Nil -> x
    (Cons y z) -> app (x (cbnExec (State y Nil))) z

state t = State t Nil

cbnEval = cbnExec . state

-----------------------------------------------
-- Examples

cyc :: Term [[Char]]
cyc = Con (:) `App` Con "k" `App` cyc
-- cyc = (:) <$> pure "k" <*> cyc

-- church encoding
newtype List a r = List { fromList :: r -> (a -> List a r -> r) -> r }

prod :: Term (List Int Int -> Int)
prod = Lam $ \l -> 
   fromList <$> l <*> Con 1 <*> (Lam $ \h -> Lam $ \t -> (*) <$> h <*> (prod <*> t) )


nil :: Term (List a r)
nil = List <$> (Lam $ \n -> Lam $ \c -> n)

cons :: Term (a -> List a r -> List a r)
cons = Lam $ \h -> Lam $ \t -> List <$> (Lam $ \n -> Lam $ \c -> c <*> h <*> t)

list1 :: Term (List Int r)
list1 = cons <*> Con 2 <*> (cons <*> Con 3 <*> nil)

test = prod <*> list1


-- why this works is a bit misterious to me. :)
main = print $ take 10 $ cbnEval cyc

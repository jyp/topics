-- This follows 

-- "A functional correspondence between
-- evaluators and abstract machines"
-- Mads Sig Ager, Dariusz Biernacki, Olivier Danvy, Jan Midtgaard

-- 2.1
data Term 
    = Ind Int
    | Abs Term
    | App Term Term


-- 2.1.1
-- Interpreter as in the paper:

data EnvVal = Thunk (() -> ExpVal)
data ExpVal = Funct (EnvVal -> ExpVal)

type Env = [EnvVal]

eval :: (Term, Env) -> ExpVal
eval (Ind n, e) = let Thunk thunk = e !! n
                   in thunk ()
eval (Abs t, e) = Funct (\v -> eval (t, v:e))
eval (App t0 t1, e) = let 
    Funct f = eval (t0, e)
    in f (Thunk (\() -> eval (t1,e)))


evalClosed t = eval (t, [])



-- Simplified interpreter (no need for thunks in haskell!)
{-
data ExpVal = Funct (ExpVal -> ExpVal) -- Values are functions.

type Env = [ExpVal]

eval :: (Term, Env) -> ExpVal
eval (Ind n, e) = e !! n
eval (Abs t, e) = Funct (\v -> eval (t, v:e))
eval (App t0 t1, e) = let 
    Funct f = eval (t0, e)
    in f (eval (t1,e))

evalClosed t = eval (t, [])


-}
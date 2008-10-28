data Term = Lam (Term -> Term) | App Term Term | Con String
--  deriving Show

parens s = "("++s++")"

-- Higher order encoding of lambda-calculus.
instance Show Term where
    showsPrec d (Con x) = showString x
    showsPrec d (Lam f) = showString "\\"
    showsPrec d (App t1 t2) = showParen (d > 1) (showsPrec 1 t1 . showString " " . showsPrec 2 t2)

data Closure = Term
  deriving Show
type Env = [Closure]
type State = (Closure, Stack)
type Stack = [Closure]

-- Adaptation of the KAM to evaluate it.
step (Lam f         , v:s)  = step (f v, s)
step (App t1 t2     , s)    = step (t1, t2:s)


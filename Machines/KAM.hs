import Text.Show
import Control.Arrow
import Data.List
import Prelude hiding (succ)
type Sym = String
data Term = Var Sym | Lam Sym Term | App Term Term | Con String
--  deriving Show

substClosed v s (Var v') = if v == v' then s else Var v'
substClosed v s (App t1 t2) = App (substClosed v s t1) (substClosed v s t2)
substClosed v s (Lam v' t) = if v == v' then Lam v' t else Lam v' (substClosed v s t)
substClosed v s (Con x) = Con x


parens s = "("++s++")"

instance Show Term where
    showsPrec d (Con x) = showString x
    showsPrec d (Var x) = showString x
    showsPrec d (Lam x t) = showParen (d > 0) (showString "\\" . showString x . showString "->" . showsPrec 0 t)
    showsPrec d (App t1 t2) = showParen (d > 1) (showsPrec 1 t1 . showString " " . showsPrec 2 t2)

data Closure = Term :+ Env
  deriving Show
type Env = [(Sym,Closure)]
type State = (Closure, Stack)
type Stack = [Closure]

lookupEnv :: Sym -> Env -> Closure
lookupEnv x [] = error $ x ++ " not found in env!"
lookupEnv x ((y,v):rho) = if x == y then v else lookupEnv x rho

step (Var x    :+ rho, s)   = Just (lookupEnv x rho, s) 
step (Lam x t  :+ rho, v:s) = Just (t :+ ((x,v):rho), s)
step (App t1 t2 :+ rho, s)   = Just (t1 :+ rho, (t2 :+ rho):s)
step _ = Nothing

dup x = (x,x)

run t = init : unfoldr (fmap dup . step) init 
    where init = (t :+ [], [])

test = mapM_ print . run 
test' = mapM_ (print . evalState) . run 

subsAll t [] = t
subsAll t ((v,s):rho) = substClosed v s (subsAll t rho)

evalClosure (t :+ rho) = subsAll t (map (second evalClosure) rho)

evalState (cl,s) = foldl1 App (map evalClosure (cl:s))
--------------------

i_ = Lam "x" (Var "x")

infixl `App`


zero = Lam "f" $ Lam "x" $ Var "x"
succ = Lam "n" $ Lam "f" $ Lam "x" $ ((Var "n") `App` (Var "f")) `App` ((Var "f") `App` (Var "x"))
two = succ `App` (succ `App` zero)
twice = Lam "f" $ Lam "x" $ (Var "f" `App` ( Var "f" `App` Var "x"))
_id = Lam "y" $ Var "y"

value1 = twice `App` _id
value2 = (twice `App` _id) `App` (Con "V")

testChurch = two `App` (Con "F") `App` (Con "X")


delta = Lam "x" $ App (Var "x") (Var "x") 


s0 = (App delta delta, [], [])



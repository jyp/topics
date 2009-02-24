\ignore{
\begin{code}
{-# LANGUAGE TypeOperators, GADTs #-}
module Progress where
import SExpr
import Stack
import Parser

mapSucc PSusp = PSusp
mapSucc (PRes x) = PRes (succ x) 
mapSucc (x :> xs) = succ x :> mapSucc xs

dislikeThreshold _ = 0

\end{code}
}


\begin{code}
data Progress = PSusp | PRes Int | Int :> Progress
\end{code}

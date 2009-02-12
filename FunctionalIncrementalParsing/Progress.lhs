\ignore{
\begin{code}
{-# LANGUAGE TypeOperators, GADTs #-}
module Progress where
import Stack
import Parser

mapSucc S = S
mapSucc (D x) = D (succ x) 
mapSucc (x :> xs) = succ x :> mapSucc xs

dislikeThreshold _ = 0

\end{code}
}


\begin{code}
data Progress = S | D Int | Int :> Progress
\end{code}

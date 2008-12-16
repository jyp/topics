\ignore{

\begin{code}
module Stack where
\end{code}

}




\begin{code}
data top :< rest = (:<) {top :: top, rest :: rest}
data Nil = Nil
infixr :<
\end{code}

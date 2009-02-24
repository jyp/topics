\ignore{
\begin{code}
{-# LANGUAGE TypeOperators, GADTs #-}
module Parser where
import SExpr
import Stack

\end{code}
}

\begin{code}
data Parser s a where
    Pure   :: a                                  -> Parser s a
    (:*:)  :: Parser s (b -> a) -> Parser s b    -> Parser s a
    Symb   :: Parser s a -> (s -> Parser s a)    -> Parser s a
    Disj   :: Parser s a -> Parser s a           -> Parser s a
    Yuck   :: Parser s a                         -> Parser s a
\end{code}

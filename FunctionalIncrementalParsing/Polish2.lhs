\ignore{
\begin{code}
{-# LANGUAGE TypeOperators, GADTs #-}
module Choice where
import SExpr
import Stack
import Parser
import Progress

\end{code}
}

\begin{code}
data Polish s a where
    Push     ::  a -> Polish s r                      ->  Polish s (a :< r)
    App      ::  Polish s ((b -> a) :< b :< r)
                                                      ->  Polish s (a :< r)
    Done     ::                                           Polish s Nil
    Shift    ::  Polish s a                           ->  Polish s a
    Sus      ::  Polish s a -> (s -> Polish s a) 
                                                      ->  Polish s a
    Best     ::  Polish s a -> Polish s a             ->  Polish s a
    Dislike  ::  Polish s a                           ->  Polish s a

toP :: Parser s a -> (Polish s r -> Polish s (a :< r))
toP (Pure x)    = Push x
toP (f :*: x)   = App . toP f . toP x
toP (Symb a f)  = \fut -> Sus  (toP a fut)
                               (\s -> toP (f s) fut)
toP (Disj a b)  = \fut -> Best (toP a fut) (toP b fut)
toP (Yuck p)    = Dislike . toP p 
\end{code}



\ignore{
\begin{code}
{-# LANGUAGE TypeOperators, GADTs #-}
module Example where
import Code
\end{code}
}

In this section we rewrite our parser for S-expressions in section \ref{sec:input} 
using disjunction and error-correction. 
The goal is to illustrate how these new constructs can help in writing more modular parser descriptions.


First, we can define repetition and sequence in the traditional way:

\begin{code}
many,some :: Parser s a -> Parser s [a]
many v = some v `Disj` Pure []
some v = Pure (:) :*: v :*: many v
\end{code}

Checking for the end of file can be done as follows. Notice that if 
the end of file is not encountered, we keep parsing the input, but
complain while doing so.

\begin{code}
eof = Symb (Pure ()) (\_ -> Yuck eof)
\end{code}

Checking for a specific symbol can be done in a similar way: we
accept anything but dislike (|Yuck|!) anything unexpected.

\begin{code}
pleaseSymbol :: Eq s => s -> Parser s (Maybe s)
pleaseSymbol s = Symb
     (Yuck $ Pure Nothing)
     (\s' ->if s == s' then Pure (Just s')
                       else Yuck $ Pure (Just s'))
\end{code}

All of the above can be combined to write the parser for S-expressions.
Note that we need to amend the result type to accommodate for erroneous inputs.

\begin{code}

data SExpr 
    = S [SExpr] (Maybe Char) 
    | Atom Char 
    | Missing 
    | Deleted Char

parseExpr = Symb
     (Yuck $ Pure Missing) 
     (\c ->case c of 
         '(' -> Pure S :*: many parseExpr :*: pleaseSymbol ')'
         ')' -> Yuck $ Pure $ Deleted ')'
         c   -> Pure $ Atom c)

parseTopLevel 
    = Pure const :*: parseExpr :*: eof
\end{code}


We have seen that the constructs introduced in this section (|Disj|, |Yuck|) 
permit to write general purpose derived combinators, such as |many|, in a
traditional style.


\ignore{
\begin{code}
{-# LANGUAGE TypeOperators, GADTs #-}
module Example where
import Choice

\end{code}
}

First, we can define repetition and sequence in the traditional way:

\begin{code}
many v = some v `Disj` pure []
some v = Pure (:) :*: v :*: many v
\end{code}

Checking for the end of file can be done as follows. Notice that if 
the end of file is not encountered, we keep parsing the input, but
complain while doing so.

\begin{code}
eof = symb (pure ()) (\_ -> Yuck eof)
\end{code}

Checking for a specific symbol can be done in a similar way: we
accept anything but be reluctant to get anything unexpected.

\begin{code}
pleaseSymbol s = symb
     (Yuck $ Pure Nothing)
     (\s' ->if s == s' then Pure (Just ')')
                       else Yuck $ Pure (Just s'))
\end{code}

All of the above can be combined to write the parser for s-expressions.
Note that we need to amend the result type to accomotate for erroneous inputs.

\begin{code}

data SExpr 
    = S [SExpr] (Maybe Char) 
    | Atom Char 
    | Missing 
    | Deleted Char

parseExpr = symb
     (oops "no input" $ pure Missing) 
     (\c ->case c of 
         '(' -> S <$> many parseExpr <*> pleaseSymbol ')'
         ')' -> Yuck $ Pure $ Deleted ')'
         c   -> pure $ Atom c)

parseTopLevel 
    = Pure const :*: parseExpr :*: eof
\end{code}


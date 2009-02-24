\ignore{
\begin{code}
{-# LANGUAGE TypeOperators, GADTs #-}
module Example where
import Code
\end{code}
}

First, we can define repetition and sequence in the traditional way:


\begin{code}

data BList a = BList ([a] -> [a]) [a]
cons  x ~(BList l r) = BList l (x:r)
cons' x ~(BList l r) = BList ((x:).l) r
nil = BList id []

toList ~(BList l r) = reverse (l []) ++ r

many v = some v `Disj` pure nil
some v = Pure2 cons' cons :*: v :*: many v
\end{code}

Checking for the end of file can be done as follows. Notice that if 
the end of file is not encountered, we keep parsing the input, but
complain while doing so.

\begin{code}
eof = Symb (pure ()) (\_ -> Yuck eof)
\end{code}

Checking for a specific symbol can be done in a similar way: we
accept anything but be reluctant to get anything unexpected.

\begin{code}
pleaseSymbol s = Symb
     (Yuck $ pure Nothing)
     (\s' ->if s == s' then pure (Just ')')
                       else Yuck $ pure (Just s'))
\end{code}

All of the above can be combined to write the parser for s-expressions.
Note that we need to amend the result type to accomotate for erroneous inputs.

\begin{code}

data SExpr 
    = S (BList SExpr) (Maybe Char) 
    | Atom Char 
    | Missing 
    | Deleted Char

type Top = BList SExpr



parseExpr = Symb
     (Yuck $ pure Missing) 
     (\c ->case c of 
         '(' -> pure S :*: parseList :*: pleaseSymbol ')'
         ')' -> Yuck $ pure $ Deleted ')'
         c   -> pure $ Atom c)

parseList = many parseExpr

parseTopLevel 
    = pure const :*: parseList :*: eof
\end{code}


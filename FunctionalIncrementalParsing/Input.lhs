\ignore{

\begin{code}
import SExpr
import Stack
\end{code}

}

\section{Adding input}
\label{sec:input}

While the study of the pure applicative language is interesting in its
own right (we come back to it in section~\ref{sec:zipper}), it is not enough
to represent parsers: it lacks dependency on the input.

We introduce an extra type argument (the type of symbols), as well as a new
constructor: |Symb|. It expresses that the rest of the expression depends on the
(first symbol of) the output.

\begin{code}
data Parser s a where
    (:*:) :: Parser s (b -> a) -> Parser s b   -> Parser s a
    Pure :: a                                  -> Parser s a
    Symb :: Parser s a -> (s -> Parser s a)    -> Parser s a
\end{code}

Using just this we can write a simple parser for S-expressions.

\begin{code}
parseList :: Parser Char [SExpr]
parseList = Symb
   (Pure [])
   (\c -> case c of
       ')'  -> Pure []
       ' '  -> parseList -- ignore spaces
       '('  -> Pure (\h t -> S h : t) :*: parseList :*: parseList
       c    -> Pure (Atom c :) :*: parseList)
\end{code}


We introduce the corresponding construct in the |Polish| expressions and amend
the translation. Intermediate results are represented by a polish expression
with a |Susp| element. The part before the |Susp| element corresponds to the
constant part that is fixed by the input already parsed. The arguments of
|Susp| contain the continuation of the parsing algorithm.

\begin{code}
data Polish s r where
    Push     :: a -> Polish s r ->                   Polish s (a :< r)
    App      ::  Polish s ((b -> a) :< b :< r)  ->   Polish s (a :< r)
    Done     ::                                      Polish s Nil
    Susp     :: Polish s r -> (s -> Polish s r) ->   Polish s r
\end{code}

\begin{spec}
  toP (Symb nil cons) = 
       \k -> Susp (toP nil k) (\s -> fromP (toP (cons s) k))
  ... (other cases unchanged)
\end{spec}

We broke the linearity of the type, but it does not matter since the parsing
algorithm will not proceed further than the available input anyway, and
therefore will stop at the first |Susp|. When the input is made available, it is
used to remove the |Susp| constructors. Suspensions in a polish expression can
be resolved by feeding input into it. When facing a suspension, we pattern match
on the input, and choose the corresponding branch in the result.

\begin{code}
feed :: [s] -> Polish s r -> Polish s r
feed ss p = case p of
                  (Susp nil cons)   -> case ss of
                      []            -> feed  []  nil
                      (s:ss')       -> feed  ss' (cons s)
                  (Push x p')      -> Push x  (feed ss p')
                  (App p')         -> App     (feed ss p')
\end{code}

|feed "(a)" (toPolish parseList)| yields back our example expression.


We can also obtain intermediate parsing results by feeding symbols one at a
time. The list of all intermediate results is constructed lazily using |scanl|.

\begin{code}
feedOne :: Polish s a -> s -> Polish s a
feedOne (Push x s)         ss  = Push x (feedOne s ss)
feedOne (App f)            ss  = App (feedOne f ss)
feedOne (Susp nil cons)    s   = cons s
\end{code}

\begin{spec}
partialParses = scanl feedOne
\end{spec}

Now, if the $(n+1)^{th}$ element of the input is changed, one can reuse
the $n^{th}$ element of the partial results list and feed it the
new input's tail (from that position).

This suffers from a major issue: partial results remain in their ``polish
expression form'', and reusing offers little benefit, because no part of the
result value (computation of evalR) is shared beyond construction of the
expression in polish form. Fortunately, it is possible to partially evaluate
prefixes of polish expressions.

The following definition performs this task by performing
applications by traversing the result and applying functions along
the way.

\begin{code}
evalL :: Polish s a -> Polish s a
evalL (Push x r) = Push x (evalL r)
evalL (App f) = case evalL f of
                  (Push a (Push b r)) -> Push (a b) r
                  r -> App r
partialParses = scanl (\c -> evalL . feedOne c)
\end{code}
This still suffers from a major drawback: as long as a function
application is not saturated, the polish expression will start with

For example, after applying the s-expr parser to the string \verb!(abcdefg!, 
|evalL| is unable to perform any simplification of the list prefix.

\begin{spec}
evalL $ feed "(abcdefg" (toPolish parseList) 
  ==  App $ Push (Atom 'a' :) $ 
      App $ Push (Atom 'b' :) $ 
      App $ Push (Atom 'c' :) $ 
      App $ ...
\end{spec}

This prefix will persist until the end of the input is reached. A
possible remedy is to avoid writing expressions that lead to this
sort of intermediate results, and we will see in section~\ref{sec:sublinear} how
to do this in the particularly important case of lists. This however works
only up to some point: indeed, there must always be an unsaturated
application (otherwise the result would be independent of the
input). In general, after parsing a prefix of size $n$, it is
reasonable to expect a partial application of at least depth
$O(log~n)$, (otherwise the parser is discarding
information).

\subsection{Zipping into Polish}
\label{sec:zipper}
Thus we have to use a better strategy to simplify intermediate
results. We want to avoid the cost of traversing the structure
up to the suspension at each step. This suggests to use a
zipper structure with the focus at the suspension point.


\begin{code}
data Zip s out where
   Zip :: RPolish stack out -> Polish s stack -> Zip s out

data RPolish inp out where
  RPush  :: a -> RPolish (a :< r) out 
                  -> RPolish r out
  RApp   :: RPolish (b :< r) out 
                  -> RPolish ((a -> b) :< a :< r) out 
  RStop  :: RPolish r r
\end{code}
The data being linear, this zipper is very similar to the zipper
for lists. The part that is already visited (``on the left''), is
reversed. Note that it contains only values and applications, since
we never go past a suspension.

The interesting features of this zipper are its type and its
meaning.

We note that, while we obtained the data type for the left part by
mechanically inverting the type for polish expressions, it can be
assigned a meaning independently: it corresponds to \emph{reverse}
polish expressions.

In contrast to forward polish expressions, which directly produce
an output stack, reverse expressions can be understood as automata
which transform a stack to another. This is captured in the type
indices |inp| and |out|.

Running this automaton on an input stack offers no surprise.
\begin{code}
evalRP :: RPolish inp out -> inp -> out
evalRP RStop acc = acc 
evalRP (RPush v r) acc = evalRP r (v :< acc)
evalRP (RApp r) (f :< a :< acc) = evalRP r (f a :< acc)
\end{code}


In our zipper type, the direct polish expression yet-to-visit
(``on the right'') has to correspond to the reverse polish
automation (``on the left''): the output of the latter has to match
the input of the former.

We capture all these properties in the types by using GADTs. This
allows properly type the traversal of polish expressions.

\begin{code}
right :: Zip s out -> Zip s out
right (Zip l (Push a r)) = Zip (RPush a l) r
right (Zip l (App r)) = Zip (RApp l) r
right (Zip l s) = (Zip l s)
\end{code}

As the input is traversed, we also simplify the prefix that we went past,
evaluating every application, effectively ensuring that each |RApp| is preceded
by at most one |RPush|.

\begin{code}
simplify :: RPolish s out -> RPolish s out
simplify (RPush a (RPush f (RApp r))) = 
             simplify (RPush (f a) r)
simplify x = x
\end{code}

We see that simplifying a complete reverse polish expression requires $O(n)$
steps, where $n$ is the length of the expression. This means that the
\emph{amortized} complexity of parsing one token (i.e. computing an partial
result based on the previous partial result) is $O(1)$, if the size of the
result expression is proportional to the size of the input. We discuss the worst
case complexity in section~\ref{sec:sublinear}.

In summary, it is essential for our purposes to have two evaluation procedures 
for our parsing results. The first one, presented in section~\ref{sec:applicative}
provides the online property, and corresponds to a call-by-name transformation
of the direct evaluation of applicative expressions. The second one, presented in
this section, enables incremental evaluation of intermediate results, and corresponds to
a call-by-value transformation of the same direct evaluation function.

% -*- latex -*-
\ignore{

\begin{code}
{-# LANGUAGE TypeOperators, GADTs #-}
module Choice where
import SExpr hiding (S)
import Stack
import Parser
import Progress

\end{code}

}
\section{Adding Choice}
\label{sec:parsing}

\comment{Characterize termination of the algorithm}

We kept the details of actual parsing out of the discussion so far.
This is for good reason: the machinery for incremental computation
and reuse of partial results is independent from such details. Indeed,
given any procedure to compute structured values from a linear
input of symbols, one can use the procedure described above to
transform it into an incremental algorithm.

\label{sec:disjunction}
\label{sec:choice}

However, parsing the input string with the interface
presented so far is highly unsatisfactory. To support convenient parsing, we can
introduce a disjunction operator, exactly as \citet{hughes_polish_2003} do: the
addition of the |Susp| operator does not undermine their treatment of
disjunction in any way.

\comment{
The zipper cannot go beyond an unresolved disjunction. That is OK
if we assume that the parser has not much look-ahead.
}

\subsection{Error correction}

\begin{figure*}
\centering
\include{progress}
\caption{
A parsing process and associated progress information. The process has been fed a whole input, so it is free of |Susp|
constructors.
It is also stripped of result information (|Push|, |App|) for conciseness, since it is irrelevant to the
computation of progress information. Each constructor is represented by a circle, and their arguments
are indicated by arrows.
The progress information associated with the process is written 
below the node that starts the process. To decide which path to take at the
disjunction (|Best|), only the gray nodes will be forced, if the desirability difference
is 1 for look-ahead 1.
}
\label{fig:progress}
\end{figure*}


Disjunction is not very useful unless coupled with \emph{failure} (otherwise any branch would
be as good as another). Still, the (unrestricted) usage of failure is
problematic for our application: the online property requires at least one
branch to yield a successful outcome. Indeed, since the |evalR| function
\emph{must} return a result (we want a total function!), the parser must
conjure up a suitable result for \emph{any} input.

If the grammar is sufficiently permissive, no error correction in the parsing
library itself is necessary. An example is the simple S-expression parser of section \ref{sec:input},
 which performs error correction in an ad-hoc way.
However, most interesting grammars produce a highly structured result, and are
correspondingly restrictive on the input they accept. Augmenting the parser with
error correction is therefore desirable.

Our approach is to add some rules to accept erroneous inputs. These will be
marked as less desirable by enclosing them with |Yuck| combinators, introduced
as another constructor in the |Parser| type. The parsing algorithm can then
maximize the desirability of the set of rules used for parsing a given fragment
of input.

%include Parser.lhs

\subsection{Example}

%include Example.lhs

\subsection{The algorithm}

Having defined our definitive interface for parsers, we can describe
the parsing algorithm itself.

As before, we linearize the applications (|:*:|) by transforming the |Parser| into a Polish-like 
representation. In addition to the the |Dislike| and |Best| constructors corresponding to |Yuck| and
|Disj|, |Shift| records where symbols have been processed, once |Susp| is removed.

%include Polish2.lhs

The remaining challenge is to amend our evaluation functions to deal with disjunction points (|Best|).
It offers two \emph{a priori} equivalent alternatives. Which one should be chosen?

Since we want online behavior, we cannot afford to look
further than a few symbols ahead to decide which parse might be the best.
(Performance is another motivation: the number of potential paths grows exponentially with
the amount of look-ahead.) We use the widespread technique \citep[chapter
8]{bird_algebra_1997} to \emph{thin out} the search after some constant, small amount of
look-ahead. 

Hughes and Swierstra's algorithm searches for the best path by direct manipulation
of the Polish representation, but this direct approach forces to transform between two normal forms:
one where the \emph{progress} nodes (|Shift|, |Dislike|) are at the head  and one where the 
result nodes (|Pure|, |:*:|) are at the head.
Therefore, we choose to use an intermediate datatype which represents the
progress information only. 
This clear separation of concerns also enables to compile the progress information into a convenient form:
our |Progress| data structure directly records how
many |Dislike| are encountered after parsing so many symbols.
It is similar to a list where the $n^{th}$ element tells how
much we dislike to take this path after shifting $n$ symbols following it,
\emph{assuming we take the best choice at each disjunction}. 

%include Progress.lhs

The difference from a simple list is that progress information may end with
success (|D|) or suspension (|S|), depending on whether the process reaches |Done| or
|Susp|.
Figure~\ref{fig:progress} shows a |Polish| structure and the associated
progress for each of its parts.
The |progress|
function below extracts the information from the |Polish| structure. 

\begin{spec}
progress :: Polish s r -> Progress
progress (Push _ p)       = progress p                          
progress (App p)          = progress p                          
progress (Shift p)        = 0 :# progress p
progress (Done)           = D 0
progress (Dislike p)      = mapSucc (progress p)                
progress (Susp _ _)       = S                               
progress (Best p q)       = snd $ better  (progress p) 
                                          (progress q)
mapSucc S = S
mapSucc (D x) = D (succ x) 
mapSucc (x :# xs) = succ x :# mapSucc xs
\end{spec}

\ignore{
\begin{code}
progress :: Polish s r -> Progress
progress (Push _ p)       = progress p                          
progress (App p)          = progress p                          
progress (Shift p)        = 0 :# progress p
progress (Done)           = D 0
progress (Dislike p)      = mapSucc (progress p)                
progress (Susp _ _)       = S                               
progress (Best _ pr _ _)  = pr
\end{code}
}

To deal with the last case (|Best|), we need to find out which of two profiles is better.
Using our thinning heuristic, given two |Progress| values corresponding to two
terminated |Polish| processes, it is possible to determine which one is best by
demanding only a prefix of each. The following function handles this task. It
returns the best of two progress information, together with an indicator of
which is to be chosen. Constructors |LT| or |GT| respectively indicates that the second or
third argument is the best, while |EQ| indicates that a suspension is reached.
The first argument (|lk|) keeps track of how much lookahead has been processed. This
value is a parameter to our thinning heuristic, |dislikeThreshold|, which indicates
when a process can be discarded.

\begin{code}
better _ S _ = (EQ, S)
better _ _ S = (EQ, S)
better _ (D x) (D y) = 
   if x <= y then (LT, D x) else (GT, D y)
better lk xs@(D x) (y:#ys) = 
   if x == 0 || y-x > dislikeThreshold lk 
   then (LT, xs) 
   else min x y +> better (lk+1) xs ys
better lk (y:#ys) xs@(D x) = 
   if x == 0 || y-x > dislikeThreshold lk 
   then (GT, xs) 
   else min x y +> better (lk+1) ys xs
better lk (x:#xs) (y:#ys)
    | x == 0 && y == 0    = rec
    | y - x > threshold   = (LT, x:#xs)
    | x - y > threshold   = (GT, y:#ys)
    | otherwise = rec
    where  threshold  = dislikeThreshold lk
           rec        = min x y +> better (lk + 1) xs ys
x +> ~(ordering, xs) = (ordering, x :# xs)
\end{code}

Calling the |better| function directly is very inefficient though, because its result is
needed every time a given disjunction is encountered. If the result of a
disjunction depends on the result of further disjunction, the result of the
further disjunction will be needlessly discarded.
Therefore, we cache the result of |better| in the |Polish| representation,
using the well known technique of \emph{tupling}. For
simplicity, we cache the information only at disjunction nodes, where we also
remember which path is best to take. 
We finally see why the |Polish| representation is important: the progress
information cannot be associated to a |Parser|, because it may depend on
whatever parser \emph{follows} it. This is not an issue in the |Polish|
representation, because applications (|:*:|) are unfolded.

We now have all the elements to write our final data structures and algorithms.
The following code shows the final construction procedure. In the |Polish| datatype, only
the |Best| constructor is amended.


\begin{spec}
data Polish s a where
    ...
    Best     ::  Ordering -> Progress -> 
                 Polish s a -> Polish s a           ->  Polish s a
\end{spec}
\ignore{
\begin{code}
data Polish s a where
    Push     ::  a -> Polish s r                      ->  Polish s (a :< r)
    App      ::  Polish s ((b -> a) :< b :< r)
                                                      ->  Polish s (a :< r)
    Done     ::                                           Polish s Nil
    Shift    ::  Polish s a                           ->  Polish s a
    Susp     ::  Polish s a -> (s -> Polish s a) 
                                                      ->  Polish s a
    Best     ::  Ordering -> Progress -> 
                 Polish s a -> Polish s a           ->  Polish s a
    Dislike  ::  Polish s a                           ->  Polish s a
\end{code}
}

\begin{code}

toP :: Parser s a -> (Polish s r -> Polish s (a :< r))
toP (Symb a f)  = \fut -> Susp  (toP a fut)
                               (\s -> toP (f s) fut)
toP (f :*: x)   = App . toP f . toP x
toP (Pure x)    = Push x
toP (Disj a b)  = \fut -> mkBest (toP a fut) (toP b fut)
toP (Yuck p)    = Dislike . toP p 

mkBest :: Polish s a -> Polish s a -> Polish s a
mkBest p q = 
   let  (choice, pr) = better 0 (progress p) (progress q) 
   in   Best choice pr p q
\end{code}

The evaluation functions can be easily adapted to support disjunction by
querying the result of |better|, cached in the |Best| constructor. We write the the
online evaluation only: partial result computation is modified similarly.

\begin{code}
evalR :: Polish s r -> r
evalR Done                   = Nil                                
evalR (Push a r)             = a :< evalR r                       
evalR (App s)                = apply (evalR s)                    
  where apply ~(f:< ~(a:<r)) = f a :< r                           
evalR (Shift v)              = evalR v                            
evalR (Dislike v)            = evalR v
evalR (Susp _ _)             = error "input pending"
evalR (Best choice _ p q)    = case choice of                     
    LT -> evalR p
    GT -> evalR q
    EQ -> error "Suspension reached"
\end{code}

Note that this version of |evalR| expects a process without any pending
suspension (the end of file must have been reached). In this version we also
disallow ambiguity, see section \ref{sec:thinning} for a discussion.

\subsection{Summary}

We have given a convenient interface for constructing error-correcting parsers,
and functions to evaluate them. This is performed in steps: first we
linearize applications into |Polish| (as in section \ref{sec:input}), then we linearize
disjunctions (|progress| and |better|) into |Progress|. The final result is computed by traversing the
|Polish| expressions, using |Progress| to choose the better alternative in disjunctions.

Our technique can also be re-formulated as lazy dynamic programming, in the style of
\citet{allison_lazy_1992}. We first define a full tree of possibilities (Polish
expressions with disjunction), then we compute progress information that we
tie to it, for each node; finally, finding the best path is a matter of looking
only at a subset of the information we constructed, using any suitable
heuristic. The cut-off heuristic makes sure that only a part of the
exponentially growing data structure is demanded. Thanks to lazy evaluation, only
that small part will be actually constructed.

\subsection{Thinning out results and ambiguous grammars}
\label{sec:thinning}

A sound basis for thinning out less desirable paths is to discard those which
are less preferable by some amount. In order to pick one path after a constant
amount of look-ahead $l$, we must set this difference to 0 when comparing the
$l^{th}$ element of the progress information, so that the parser can pick a
particular path, and return results. Unfortunately, applying this rule strictly
is dangerous if the grammar requires a large look-ahead, and in particular if
it is ambiguous. In that case, the algorithm can possibly commit to a prefix which will
lead to errors while processing the rest of the output, while another prefix
would match the rest of the input and yield no error. In the present version of
the library we avoid the problem by keeping all valid prefixes.
The user of the parsing library has to be aware of this issue when designing
grammars: it can affect the performance of the algorithm to a great extent,
by triggering an exponential explosion of possible paths.






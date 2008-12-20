\ignore{

\begin{code}
{-# LANGUAGE TypeOperators, GADTs #-}
module Choice where
import SExpr
import Stack

\end{code}

}
\section{Eliminating linear behavior}
\label{sec:sublinear}

As we noted in a section~\ref{sec:input}, partial computations sometimes
cannot be performed. 


This is indeed a very common case: if the
output we construct is a list, then the spine of the list can only
be constructed once we get hold of the very tail of it. 

For example, our parser for s-expressions would produce such lists for for flat
expressions, because the applications of |(:)| can be computed only when the end of the
input is reached.

\begin{spec}
evalL $ feed "(abcdefg" (toPolish parseList) 
  ==  App $ Push (Atom 'a' :) $ 
      App $ Push (Atom 'b' :) $ 
      App $ Push (Atom 'c' :) $ 
      App $ ...
\end{spec}

Section~\ref{sec:zipper} explained how to optimize the creation of intermediate
results, by skipping this prefix. 

Unfortunately this does not improve the asymptotic performance of computing the
final result. The bottom-most partial result contains the long chain of partial
applications (in reverse polish representation). To produce the final result the
whole prefix has to be traversed.

Therefore, in the worst case, the construction of the result has a cost
proportional to the length of the input. 


The insight that helps solving the issue is that the culprit for linear complexity is 
the linear shape of the list. Fortunately, nothing forces to use such a structure: it
can always be replaced by a tree structure, which can then be traversed in pre-order
to discover the elements in the same order as for the corresponding list.
\citet[section 7]{wagner_efficient_1998} recognize this
issue and propose to replace left or right recursive rules in the parsing with a
special repetition construct. The parsing algorithm treats this construct
specially and does re-balancing of the tree as needed. We choose a different
approach, which builds upon the combinators we have introduced so far. The
advantage is that we do not need to complicate, not change at all, the parsing
algorithms.

As \citet{wagner_efficient_1998}, we produce a different data structure for the
output, but the difference are that our basic combinators are powerful enough to
produce this data structure with no modification: this is because we can
parameterize our parsing rules by haskell values (for free), and because we have
no tree update.

Let us summarize the requirements we put on the data structure:

\begin{itemize}
\item
  It must provide the same laziness properties as a list: accessing
  an element in the structure should not force to parse the input
  further than necessary if we had used a list.

\item
  the $n^{th}$ element in pre-order should not be further away than
  $O(log~n)$ elements from the root of the structure. In other words,
  if such a structure contains a suspension in place of an element at
  position $n$, there will be no more than $O(log~n)$ partial
  applications on the stack of the corresponding partial result. This
  in turn means that the resuming cost for that partial result will
  be in $O(log~n)$.

\end{itemize}
The second requirement suggests a tree-like structure, and the first
requirement implies that whether the structure is empty or not can
be determined by entering only the root constructor. It turns out that
a simple binary tree can fulfill these requirements.

\label{tree_structure}
\begin{code}
data Tree a  = Node a (Tree a) (Tree a)
             | Leaf
\end{code}
The only choice that remains is the size of the subtrees. The
specific choice we make is not important as long as we make sure
that each element is reachable in $O(log~n)$ steps. A simple choice
is have a list of complete trees with increasing depth $k$,
yielding a tree of size sizes $2^{k} - 1$. To make things more
uniform we can encode the list using the same datatype.


\begin{figure}
\include{tree}
\caption{
A tree storing the elements 1 \ldots{} 14
}
\label{fig:online_tree}
\end{figure}


A complete tree of total depth $2 d$ can therefore store at least
$\sum_{k=1}^d 2^{k}-1$ elements, fulfilling the second
requirement.

This structure is very similar to binary random access lists as presented by
\citet[section~6.2.1]{okasaki_purely_1999}, but differ in purpose. In our case
we want to construct the list in one go, without pattern matching on our arguments.
(ie. we want the argument to Pure to be a constructor). Indeed, the construction 
procedure is the only novel idea we introduce:


\begin{code}
toTree d [] = Leaf
toTree d (x:xs) = Node x l (toTree (d+1) xs')
    where (l,xs') = toFullTree d xs

toFullTree 0 xs = (Leaf, xs)
toFullTree d [] = (Leaf, [])
toFullTree d (x:xs) = (Node x l r, xs'')
    where  (l,xs' ) = toFullTree (d-1) xs
           (r,xs'') = toFullTree (d-1) xs'
\end{code}

\textmeta{In fact, we will have to construct the list directly in the parser,
as follows:}

\subsection{Quick access}

A key observation is that, given the above structure, one can
access an element without pattern matching on any other node that
is not the direct path to it. This allows efficient access without
loosing any property of laziness. Thus, we can avoid the other
source of inefficiencies of our implementation.

\begin{enumerate}[1.]
\item
  We can fetch the partial result that corresponds to the user change
  without traversing the whole list of partial results or forcing its
  length to be computed. Of course, the first time it is accessed
  intermediate results up to the one we require still have to be
  computed.

\item
  The final results that the user observe will be in linear form as
  well. We don't want to store them in a structure that forces the
  length, otherwise our parser will be forced to process the whole
  input. Still, we want to access the part corresponding to the
  window being viewed efficiently. Storing the results in the same
  type of structure saves the day again.

\end{enumerate}

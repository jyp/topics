\ignore{

\begin{code}
{-# LANGUAGE TypeOperators, GADTs #-}
module Sublinear where
import SExpr
import Stack
import Choice

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

The culprit for linear complexity is 
the linear shape of the list. Fortunately, nothing forces to use such a structure: it
can always be replaced by a tree structure, which can then be traversed in pre-order
to discover the elements in the same order as in the corresponding list.
\citet[section 7]{wagner_efficient_1998} recognize this
issue and propose to replace left or right recursive rules in the parsing with a
special repetition construct. The parsing algorithm treats this construct
specially and does re-balancing of the tree as needed. We choose a different
approach, which builds upon the combinators we have introduced so far. We 
produce such a tree without complication, nor any modification of library
because it is based on combinators: we can parameterize our parsing by
arbitray values, for free. Also, since we do not update a tree, but
produce a fresh version every time, we need not worry about re-balancing issues.

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
is a series of complete trees of increasing depth. The $k^{th}$ tree
will have depth $k$ and contain $2^{k} - 1$ nodes. For simplicity, all these subtrees
are chained using the same data type: they are attached as the left child
of the spine of a right-leaning linear tree. Such a structure is depicted in
figure~\ref{fig:online_tree}.


\begin{figure}
\include{tree}
\caption{
A tree storing the elements 1 \ldots{} 14
}
\label{fig:online_tree}
\end{figure}


We note that a complete tree of total depth $2 d$ can therefore store at least
$\sum_{k=1}^d 2^{k}-1$ elements, fulfilling the second
requirement.

This structure is very similar to binary random access lists as presented by
\citet[section~6.2.1]{okasaki_purely_1999}, but differ in purpose. In our case
we want to construct the list in one go, without pattern matching on our
arguments. Indeed, the construction procedure is the only
novel idea we introduce:


\begin{code}
toTree d []      = Leaf
toTree d (x:xs)  = Node x l (toTree (d+1) xs')
    where (l,xs') = toFullTree d xs

toFullTree 0 xs       = (Leaf, xs)
toFullTree d []       = (Leaf, [])
toFullTree d (x:xs)   = (Node x l r, xs'')
    where  (l,xs' )  = toFullTree (d-1) xs
           (r,xs'')  = toFullTree (d-1) xs'
\end{code}

In extenso, we must do this to guarantee online production of results: we want
the argument of |Pure| to be in a simple value (not an abstraction), as explained in
section~\ref{sec:applicative}. In fact, we will have to construct the list directly in the parser,
as follows.


\begin{code}
parseTree d = Symb
       (Pure Leaf)
       (\s -> Pure (Node s) :*: 
           parseFullTree d :*: 
           parseTree (d+1))

parseFullTree 0 = Pure Leaf
parseFullTree d = Symb 
       (Pure Leaf) 
       (\s -> Pure (Node s) :*: 
           parseFullTree (d-1) :*: 
           parseTree (d-1))
\end{code}

\textmeta{What if we parse something else than symbols? Left out.}

\begin{spec}
parseTree d p = (pure Leaf) 
   :|: (  Pure Node 
          :*: p 
          :*: parseFullTree d 
          :*: parseTree (d+1))
parseFullTree p 0 = pure Leaf
   :|: (  Pure Node 
          :*: p 
          :*: parseFullTree (d-1) 
          :*: parseTree (d-1))
\end{spec}


\subsection{Quick access}

There is an other source of inefficiency caused by the use of lists:
merely finding the part of the tree corresponding to the edition window
takes linear time. 

Fortunately, this issue is solved as well by using
the tree structure described above.
Indeed,the size of each subtree depends only on its
relative position to the root. Therefore, one can access an element by its index
without pattern matching on any node which is not the direct path to it.
This allows efficient indexed access without loosing any property of laziness. 


In our application, there is yet another structure that can benefit from 
the usage of this tree structure: the list of intermediate results. Indeed,
while we have shown that the computation of a new partial result is efficient,
the mere search for the previous partial result that we can reuse can take
linear time, if we store partial results for every point of the input
in a list.


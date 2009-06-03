\ignore{

\begin{code}
{-# LANGUAGE TypeOperators, GADTs #-}
module Sublinear where
import SExpr
import Stack
import Parser

\end{code}

}
\section{Eliminating linear behavior}
\label{sec:sublinear}

As we noted in section~\ref{sec:input}, the result of some computations
cannot be pre-computed in intermediate parser states, because constructors are only partially applied. 

This is indeed a common case: if the
constructed output is a list, then the spine of the list can only
be constructed once we get hold of the very tail of it. 

For example, our parser for S-expressions would produce such lists for flat
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
final result. The partial result corresponding to the end of input contains the long chain of partial
applications (in reverse Polish representation), and to produce the final result the
whole prefix has to be traversed.

Therefore, in the worst case, the construction of the result has a cost
proportional to the length of the input. 

While the above example might seem trivial, the same result applies to all
repetition constructs, which are common in language descriptions. For
example, a very long Haskell file is typically constituted of a very long list
of declarations, for which a proportional cost must be paid every time the result
is constructed.

The culprit for linear complexity is 
the linear shape of the list. Fortunately, nothing forces to use such a structure: it
can always be replaced by a tree structure, which can then be traversed in pre-order
to discover the elements in the same order as in the corresponding list.
\citet[section 7]{wagner_efficient_1998} recognize this
issue and propose to replace left or right recursive rules in the parsing with a
special repetition construct. The parsing algorithm treats this construct
specially and does re-balancing of the tree as needed. We choose a different
approach: only the result type is changed, not the parsing library.
We can do so for two reasons:
\begin{itemize}
 \item Combinators can be parametrized by arbitrary values
 \item Since we do not update a tree, but
 produce a fresh version every time, we need not worry about re-balancing issues.
\end{itemize}

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
data Tree a  =  Node a (Tree a) (Tree a)
             |  Leaf
\end{code}
The only choice that remains is the size of the sub-trees. The
specific choice we make is not important as long as we make sure
that each element is reachable in $O(log~n)$ steps. A simple choice
is a series of complete trees of increasing depth. The $k^{th}$ tree
will have depth $k$ and contain $2^{k} - 1$ nodes. For simplicity, all these sub-trees
are chained using the same data type: they are attached as the left child
of the spine of a right-leaning linear tree. Such a structure is depicted in
figure~\ref{fig:online_tree}.


\begin{figure}
\include{pgf-tree}
\caption{
A tree storing the elements 1 \ldots{} 14. Additional elements would be
attached to the right child of node 7: there would be no impact on the 
tree constructed so far.
}
\label{fig:online_tree}
\end{figure}


We note that a complete tree of total depth $2 d$ can therefore store at least
$\sum_{k=1}^d 2^{k}-1$ elements, fulfilling the second
requirement.

This structure is very similar to binary random access lists as presented by
\citet[section~6.2.1]{okasaki_purely_1999}, but differ in purpose. 
The only construction primitive presented by Okasaki is the appending of
an element. This is of no use to us, because the function has to 
analyze the structure it is appending to, and is therefore strict.
We want avoid this, and thus must construct the structure in one go.
Indeed, the construction procedure is the only
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

In other words, we must use a special construction function to guarantee the online production of results: we want
the argument of |Pure| to be in a simple value (not an abstraction), as explained in
section~\ref{sec:applicative}. In fact, we will have to construct the list directly in the parser.

The following function implements such a parser where repeated elements are mere symbols. 


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

The function can be adapted for arbitrary non-terminals. One has to take care to avoid interference between the
construction of the shape and error recovery. For example, the position of non-terminals can be forced in the tree,
as to be in the node corresponding to the position of their first symbol. In that case the structure has to be 
accommodated for nodes not containing any information.


\subsection{Quick access}

Another benefit of using the tree structure as above is that
finding the part of the tree of symbols corresponding to the edit window
also takes logarithmic time. 
Indeed, the size of each sub-tree depends only on its
relative position to the root. Therefore, one can access an element by its index
without pattern matching on any node which is not the direct path to it.
This allows efficient indexed access without loosing any property of laziness. 
Again, the technique can be adapted for arbitrary non-terminals. However, it
will only work if each node in the tree is ``small'' enough. Finding the first
node of interest might force an extra node, and in turn force parsing the corresponding
part of the file.


\ignore{
% This is inconsistent with the example we give in an early section.

In our application, there is yet another structure that can benefit from the
usage of this lazily constructed tree: the list of intermediate results. Indeed, while we
have shown that the computation of a new partial result is efficient, the mere
search for the previous partial result that we can reuse can take linear time,
if we store partial results for every point of the input in a list. Again, since
the length the length of the input cannot be forced, we have to use the lazy
construction procedure.
}
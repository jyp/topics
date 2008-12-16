% -*- latex -*-
\documentclass[preprint]{sigplanconf}
%include lhs2TeX.fmt
%format :*: = " \applbind"
%format +> = " \secondPush"
\usepackage{amsmath}
\usepackage[mathletters]{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{graphicx}
\usepackage{pgf}
\usepackage{tikz}
\setlength{\parindent}{0pt}
\setlength{\parskip}{3pt}
\usepackage{enumerate}
% \usepackage[sort&compress,numbers]{natbib}
\usepackage[sort&compress]{natbib}
\newcommand{\ignore}[1]{}
\providecommand{\TODO}[1]{\footnote{#1}}
\providecommand{\annot}[1]{\marginpar{\footnotesize \raggedright #1}}
\newcommand{\applbind}{\mathbin{:\!\!*\!\!:}}
\newcommand{\secondPush}{\mathbin{+\!\!>}}

\newenvironment{meta}{%
\begin{quote}
\sf
}{%
\end{quote}
}

\providecommand{\textmeta}[1]{\begin{quote}\textsf{{#1}}\end{quote}}

\begin{document}

\titlebanner{Work in progress}        % These are ignored unless
\preprintfooter{In preparation for ICFP09}   % 'preprint' option specified.

\title{Lazy Functional Incremental Parsing}

\authorinfo{Jean-Philippe Bernardy}


\maketitle
\textmeta{actually it probably applies only to free-form editors of structured documents?}
\begin{abstract}
In the context of an interactive application where the user
observes only a small portion of the output, we show that combining
lazy evaluation and caching of intermediate (partial) results
enables to parse the input incrementally. We also introduce a general purpose,
simple data structure, to eliminate the linear complexity caused
by lazy lists traversals while retaining its lazy properties.
Finally, we complete our exposition of incremental parsing in an
interactive system by showing how our parsing machinery can be
improved to support error-correction.
\end{abstract}

\category{D.3.4}{Programming Languages}{Processors}
\category{D.2.3}{Coding Tools and Techniques}{Program editors}
\category{D.1.1}{Programming Techniques}{Applicative (Functional) Programming}
\category{F.3.2}{Logics and Meanings of Programs}{Semantics of Programming Languages}

\terms
Algorithms, Languages, Design, Performance, Theory

\keywords
Functional Programming, Lazy evaluation, Incremental Computing, Parsing,
Dynamic Programming, Polish representation, Editor, Haskell


\section{Introduction}

Yi \citep{bernardy_yi:editor_2008,stewart_dynamic_2005} is an editor is written
in Haskell. It provides features such as syntax highlighting and indentation
hints for the Haskell language. In order to implement all syntax-dependent
functions in a consistent way, the abstract syntax tree (AST) is available at
all times, kept up to date as the user types. In order to maintain acceptable
performance, the editor must not parse the whole file at each keystroke.

\subsection{Example}

For the purpose of illustration, we demonstrate how the
technique works on a simple problem: interactive feedback of
parenthesis matching for a lisp-like language. Given an input such
as \verb!(+ 1 (* 5 (+ 3 4)) 2)!, the program will display
\verb!(+ 1 {* 5 [+ 3 4]} 2)!. The idea is that matching pairs are
displayed using different parenthetical symbols for each level,
making the extent of each sub-expression more apparent.

The production of the output is a two-phase process. First, the AST
is produced, by parsing the input. A value of the |SExpr| type
is constructed. Second, it is linearized back and
printed to the user.

%include SExpr.lhs

\begin{figure}
\includegraphics[width=\columnwidth]{begin}
\caption{Viewing the beginning of a file. 
The triangle represents the syntax tree. The line at the bottom represents the
file. The zagged part indicates the part that is parsed. The viewing window is
depicted as a rectangle.
}
\label{fig:begin}
\end{figure}

The initial situation is depicted in figure~\ref{fig:begin}. The user views the
beginning of the file. To display the decorated output, the program
has to traverse the first few nodes of the syntax tree (in
pre-order). This in turn forces parsing the corresponding part of
the output, but \emph{only so far} (or maybe a few tokens ahead,
depending on the amount of lookahead required). If the user modifies
the input at this point, it invalidates the AST, but discarding it and
re-parsing is not too costly: only a screenful of parsing needs to be
re-done.

\begin{figure}
\includegraphics[width=\columnwidth]{mid}
\caption{
Viewing the middle of a file. 
Although only a small amount of the
parse tree may be demanded, parsing must start from the beginning of the
file.}
\label{fig:mid}
\end{figure}

As the user scrolls down in the file, more and more of the AST is demanded, and
the parsing proceeds in lockstep (figure~\ref{fig:mid}). At this stage, a user
modification is more serious: re-parsing naively from the beginning can be too
costly for a big file. Fortunately we can again exploit the linear behaviour of
parsing algorithms to our advantage. Indeed, if we have stored the parser state
for the input point where the user made the modification, we can \emph{resume}
parsing from that point. If we make sure to store partial results for every
other point of the input, we can ensure that we will never parse more than a
screenful at a time.

List of constraints 
\begin{itemize}
\item pure
\item parser-combinator library 
\end{itemize}
List of consequences
\begin{itemize}
\item maximize the use of lazy evaluation
\item error correction
\item 
\end{itemize}

In an interactive system, a lazy evaluation strategy provides a
special form of incremental computation: the amount of output that
is demanded drives the computation to be performed. In other words,
the system responds to incremental movements of the portion of the
output being viewed by the user (window) by incremental computation
of the intermediate structures.

The above observation suggests that we can take advantage of lazy evaluation to
implement incremental parsing for an interactive application.
Indeed, if we suppose that the user makes changes in the input that
``corresponds to'' the window being viewed, it suffices to cache
partially computed results for each point in the input, to obtain a
system that responds to changes in the input independently of the
total size of that input.


\subsection{Contributions}

\begin{itemize}
\item

  We describe a novel, purely functional approach to incremental parsing, which
  makes essential use of lazy evaluation. This is achieved by
  combinining online parsers with caching of intermediate
  results.

\item
  We complete our treatment of incremental parsing with 
  error correction. This is essential, since online parsers
  need to be \emph{total}: they cannot fail on any input;

\item
  We craft a data structure to be used in place of lists, which is
  more efficient but has the same properties for laziness;

\item
  We have implemented such a system in a parser-combinator library;

\item
  We have implemented such a system and made use of it to provide
  syntax-dependent feedback in a production-quality editor.

\end{itemize}

The rest of the paper describes how to build the parsing library step by
step: production of results in a online way (section~\ref{sec:applicative}), map the
input to these results and manage the incremental computation of intermediate
state (section~\ref{sec:input}), treat disjunction and error correction. In
section~\ref{sec:sublinear} we will tackle the problem of incremental parsing of
repetition. We discuss and compare our approach to alternatives in
section~\ref{sec:relatedWork} and conclude (section \ref{sec:conclusion}).
    
%include Applicative.lhs

\section{Adding input}
\label{sec:input}

While the study of the pure applicative language is interesting in its
own right (we come back to it in section~\ref{sec:zipper}), it is not enough
to represent parsers: it lacks dependency on the input.

We introduce an extra type argument (the type of symbols), as well as a new
constructor: |Case|. It expresses that the rest of the expression depends on the
(first symbol of) the output.

\begin{code}
data Parser s a where
    (:*:) :: Parser s (b -> a) -> Parser s b -> Parser s a
    Pure :: a -> Parser s a
    Case :: Parser s a -> (s -> Parser s a) -> Parser s a
\end{code}

Using just this we can write a simple parser for S-expressions.

\begin{code}
parseList :: Parser Char [SExpr]
parseList = Case 
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
  toP (Case nil cons) = 
       \k -> Susp (toP nil k) (\s -> fromP (toP (cons s) k))
  ... ( other cases unchanged)
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
                  (Sus nil cons)   -> case ss of
                      []            -> feed  []  nil
                      Just (s:ss')  -> feed  ss' (cons s)
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

partialParses = scanl feedOne
\end{code}
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
data Zip out where
   Zip :: RPolish stack out -> Polish stack -> Zip out

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

\section{Parsing}
\label{sec:parsing}
\textmeta{Termination if there is no recursive call before parsing one token}

We kept the details of actual parsing out of the discussion so far.
This is for good reason: the machinery for incremental computation
and reuse of partial results is independent from such details. Indeed,
given any procedure to compute structured values from a linear
input of symbols, one can use the procedure described above to
transform it into an incremental algorithm.

\subsection{Disjunction}
\label{sec:disjunction}

However, the most common way to produce such structured values is
by \emph{parsing} the input string. To support convenient parsing,
we can introduce a disjunction operator, exactly as \citet{hughes_polish_2003}
do: the addition of the |Susp| operator does not
undermine their treatment of disjunction in any way.

\begin{meta}
The zipper cannot go beyond an unresolved disjunction. That is OK
if we assume that the parser has not much lookahead.
\end{meta}

\subsection{Error correction}


Disjuction is not very useful unless coupled with \emph{failure} (otherwise all
branches would be equivalent). Still, the (unrestricted) usage of failure is
problematic for our application: the online property requires at least one
branch to yield a successful outcome. Indeed, since the |evalR| function
\emph{must} return a result (we want a total function!), the parser must a
conjure up a suitable result for \emph{any} input.

If the grammar is sufficiently permissive, no error correction in the parsing
algorithm itself is necessary. This is the case for our simple s-expression parser.
However, most interesting grammars produce a highly structured result, and are
correspondingly restrictive on the input they accept. Augmenting the parser with
error correction is therefore desirable.

We can do so by introducing an other constructor in the |Parser| type to denote
less desirable parses. The intent is to extend the grammar with more permissive rules
to deal with incorrect input, tagging those as less desirable. The parsing algorithm
can then maximize the desirability of the set of rules used for parsing a given
fragment of input.

\begin{code}
data Parser s a where
    Pure   :: a                                  -> Parser s a
    (:*:)  :: Parser s (b -> a) -> Parser s b    -> Parser s a
    Case   :: Parser s a -> (s -> Parser s a)    -> Parser s a
    Disj   :: Parser s a -> Parser s a           -> Parser s a
    Yuck   :: Parser s a                         -> Parser s a
\end{code}

At each disjunction point, the evaluation function will have to choose between
two alternatives. Since we want online behavior, we cannot afford to look
further than a few symbols ahead to decide which parse might be the best.
(Additionally the number of potential recovery paths grows exponentially with
the amount of lookahead). We use the widespread technique \citep[chapter
8]{bird_algebra_1997} to thin out search after some constant, small amount of
lookahead.


\begin{figure*}
\include{progress}
\caption{
A parsing process and associated progress information. The process has been fed a whole input, so it is free of |Susp|
constructors.
It is also stripped of result information for clarity (|Push|, |App|), since it is irrelevant to the
computation of progress information. Each constructor is represented by a circle, and their arguments
by arrows.
The progress information accociated with the process is written in the rectangle
beside the node that starts the process. To decide which path to take at the
disjunction, only the gray nodes will be forced, if the desirability difference
is 1 for lookahead 1.
}
\label{fig:progress}
\end{figure*}

In contrast to \citet{hughes_polish_2003}, we do not compute the best path by
direct manipulation of the polish representation. Instead, we introduce a new
datatype which represents the ``progress'' information only.

\begin{code}
data Progress = PSusp | PRes Int | !Int :> Progress
\end{code}

\textmeta{Oops, We can't really use |fix Dislike| for failure, because we use
Ints, instead of Peano naturals.}

This data structure is similar to a list where the $n^{th}$ element tells how
much we dislike to take this path after shifting $n$ symbols following it,
\emph{assuming we take the best choice at each disjunction}.

The difference with a simple list is that progress information may end with
success or suspension, depending on whether the process reaches |Done| or
|Susp|.

Given two (terminated) |Progress| values, it is possible to determine which one
is best by demanding only a prefix of each, using our thinning heuristic. 

We can now use this information to determine which path to take when facing a
disjunction. In turn, this allows to compute the progress information on the
basis of the polish representation only.


\begin{figure}
\begin{code}
data Polish s a where
    Push     ::  a -> Polish s r                      ->  Polish s (a :< r)
    App      ::  Polish s ((b -> a) :< b :< r)
                                                      ->  Polish s (a :< r)
    Done     ::                                           Polish s Nil
    Shift    ::  Polish s a                           ->  Polish s a
    Sus      ::  Polish s a -> (s -> Polish s a) 
                                                      ->  Polish s a
    Best     ::  Ordering -> Progress -> 
                   Polish s a -> Polish s a           ->  Polish s a
    Dislike  ::  Polish s a                           ->  Polish s a

progress :: Polish s r -> Progress
progress (Push _ p)       = progress p                          
progress (App p)          = progress p                          
progress (Shift p)        = 0 :> progress p                     
progress (Done)           = PRes 0
progress (Dislike p)      = mapSucc (progress p)                
progress (Sus _ _)        = PSusp                               
progress (Best _ pr _ _)  = pr                                  

toP (Case a f)  = \fut -> Sus  (toP a fut)
                               (\s -> toP (f s) fut)
toP (f :*: x)   = App . toP f . toP x
toP (Pure x)    = Push x
toP (Disj a b)  = \fut -> mkBest (toP a fut) (toP b fut)
toP (Yuck p)    = Dislike . toP p 

mkBest :: Polish s a -> Polish s a -> Polish s a
mkBest p q = 
   let  (choice, pr) = better 0 (progress p) (progress q) 
   in   Best choice pr p q

better :: Progress -> Progress -> (Ordering, Progress)
-- compute which progress is the better one, and return it.
\end{code}
\caption{Handling disjunction}
\end{figure}

Proceeding exactly as such is horribly inefficient. We can use the classic
trick \cite{swierstra} to cache the progress information in the |Polish|
representation. For simplicity, we cache the information only at disjunction
nodes where we also remember which path is best to take.

We finally see why the |Polish| representation is so important:
the progress information cannot be associated to a |Parser|, because
it may depend on whatever parser \emph{follows} it. This is not
an issue in the |Polish| representation, because it is unfolded until
the end of the parsing.


Our technique can be re-formulated as lazy dynamic programming, in the style of
\citet{allison_lazy_1992}. We first define a full tree of possibilities (Polish
expressions with disjunction), then we compute a progress information that we
tie to it, for each node; finally, finding the best path is a matter of looking
only at a subset of the information we constructed, using any suitable
heuristic. The cut-off heuristic makes sure that only a part of the
exponentially big data structure is demanded. Thanks to lazy evaluation, only
that small will be actually constructed.

\subsection{Thinning out results and ambiguous grammars}

A sound basis for thinnig out less desirable paths is to discard those which
are less preferrable by some amount. In order to pick one path after a constant
amount of lookahead $l$, we must set this difference to 0 when comparing the
$l^{th}$ element of the progress information, so that the parser can pick a
particular path, and return results. Unfortunately, applying this rule strictly
is dangerous in if the grammar requires a large lookahead, and in particular if
it is ambiguous. In that case, the algorithm can possibly commit to a prefix which will
lead to errors while processing the rest of the output, while another prefix
would match the rest of the input and yield no error. In the present version of
the library we avoid the problem by keeping all valid prefixes.

\begin{code}
better :: Int -> Progress -> Progress -> (Ordering, Progress)
better _ PSusp _ = (EQ, PSusp)
better _ _ PSusp = (EQ, PSusp)
better _ (PRes x) (PRes y) = 
   if x <= y then (LT, PRes x) else (GT, PRes y)
better lk xs@(PRes x) (y:>ys) = 
   if x == 0 || y-x > dislikeThreshold lk 
   then (LT, xs) 
   else min x y +> better (lk+1) xs ys
better lk (y:>ys) xs@(PRes x) = 
   if x == 0 || y-x > dislikeThreshold lk 
   then (GT, xs) 
   else min x y +> better (lk+1) ys xs
better lk (x:>xs) (y:>ys)
    | x == 0 && y == 0 = rec
    | y - x > threshold = (LT, x:>xs)
    | x - y > threshold = (GT, y:>ys)
    | otherwise = rec
    where threshold = dislikeThreshold lk
          rec = min x y +> better (lk + 1) xs ys
x +> ~(ordering, xs) = (ordering, x :> xs)
\end{code}


The user of the parsing library has to be aware of this issue when designing
grammars: it can affect the performance of the algorithm to a great extent.

\textmeta{Final version of evalL?}

\section{Eliminating linear behavior}
\label{sec:sublinear}

As we noted in a section~\ref{sec:input}, partial computations sometimes
cannot be performed. This is indeed a very common case: if the
output we construct is a list, then the spine of the list can only
be constructed once we get hold of the very tail of it. In
particular, our system will behave very badly for a parser that
returns its input unmodified, as a list of tokens:

\begin{code}
identity = case_  (Pure []) 
                  (\c -> Pure (:) :*: Pure c :*: identity)
\end{code}

The applications of |(:)| can be computed only when the end of the input is
reached, and at that moment the construction of the result as a cost
proportional to the length of the input. The bottom-most partial result contains
such a long chain of partial applications, and using it does not improve the
asymptotic performance of computing the final result.

The key insight is that the performance problems come from the linearity of the
output list, and we can always use a tree whose structure can be ignored when
traversing the result. \citet[section 7]{wagner_efficient_1998} recognize this
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
  the $n^{th}$ element in a list should not be further away than
  $O(log~n)$ elements from the root of the structure. In other words,
  if such a structure contains a suspension in place of an element at
  position $n$, there will be no more than $O(log~n)$ partial
  applications on the stack of the corresponding partial result. This
  in turn means that the resuming cost for that partial result will
  be in $O(log~n)$.

\end{itemize}
The second requirement suggests tree-like structure, and the first
requirement implies that whether the structure is empty or not can
be determined by entering only the root constructor. This suggests
the following data type, with the idea that it will be traversed in
preorder.

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
A tree storing the elements 0 \ldots{} 6
}
\label{fig:online_tree}
\end{figure}


A complete tree of total depth $2 d$ can therefore store at least
$\sum_{k=1}^d 2^{k}-1$ elements, fulfilling the second
requirement.

This structure is very similar to binary random access lists as presented by
\citet[section~6.2.1]{okasaki_purely_1999}, but differ in purpose. In our case
we want to construct the list in one go, without pattern matching on our arguments.
(ie. we want the argument to Pure to be a constructor)


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
\section{Related work}
\label{sec:relatedWork}

The litterature on incremental analysis of programs is so abundant that a
complete survey would deserve its own treatment. Here we will compare our
approach to some representatives alternatives only.

\subsection{Incremental parsing in development environments} 


\citet{ghezzi_incremental_1979}
\citet{ghezzi_augmenting_1980}
\citet{wagner_efficient_1998} 
\citet{bahlke_psg_1986} 


State matching approaches.
This does not apply for combinator parser library, because the parser
state is not really observable.


We have a much more modest approach, in the sense that we do not attempt to
reuse the (right-bound) nodes that were created in previous parsing runs. Another drawback is
that we assume that the window moves by incremental steps. If the user jumps
back and forth the beginning and the end of the file, while making changes at
the beginning, our approach will force reparsing the whole file every time a
change is made at the beginning followed by a jump to the end of the file.


Despite extensive research dating as far back as 30 years ago, somehow, none of
these solutions have caught up in the mainstream. Editors typically work using
regular expressions for syntax highlighting at the lexical level (Emacs, Vim,
Textmate, \ldots{}) and integrated development environments run a full compiler
in the background for syntax level feedback (Eclipse).

We might argue that early solutions offered little
benefit in comparison to their implementation cost. Our approach is
much simpler. 

One might argue that node reuse is an essential component of incremental
parsing. However, it is notable that programming languages syntaxes are often
specified with a forward reading approach. A consequence is that a small change
in the beginning of the file can completely invalidate the parse tree obtained
in the previous run. A simple example is the opening of a comment. (For example,
while editing an Haskell source file, typing \verb!{-! implies that the rest of
the file becomes a comment up to the next \verb!-}!.) Hence, trying to reuse
right-bound parts of the parse tree seems to be optimizing for a special case.
This is not very suitable in an interactive system where users expect consistent
response times.

\textmeta{A possible solution to that would be to have a parse result for every
possible prefix. Need this be mentioned?}

Another downside of our approach is that it requires the consumption of the AST
to be done in pre-order. If this is not the case, the online property becomes
useless. For example, if one wishes to apply a sorting algorithm before
displaying the output, this will force the whole input to be parsed before
displaying the first element of the input. In particular, the arguments to the
|Pure| constructor must not perform such operations on its arguments. Ideally,
it should be a simple constructor. This leaves many opportunites for the user of
the library to destroy its incremental properties.

\subsection{Incremental parsing in natural language processing} 

In natural language processing, a parsing alagorithm is deems incremental if it
reads the input one token at a time and calculates all the possible consequences
of the token, before the net token is read. (Citation? (quoted from Krasimir))

We note that there is no notion of AST update in this definition.

\textmeta{Krasimir: Does this correspond to the online property or the other?}

\subsection{Incremental computation}

An alternative approach would be to build the system on top of a generic
incremental computation system. Downsides are that there currently exists no
such off-the-shelf system for Haskell. The closest matching solution is provided
by \citet{carlsson_monads_2002} relies heavily on explicit threading of
computation through monads and explict reference for storage of inputs or
intermediate results. In our case, not only the contents of the inputs will
change, but also their number.

\begin{meta}
Plugging an attribute evaluator on top of this?
\citet{saraiva_functional_2000}
\end{meta}


\subsection{Parser combinators}

Our approach is in the tradition of parser combinator libraries, in
particular as described by \citet{hughes_polish_2003}.

The introduction of the |Susp| operator is directly inspired by
\citet{claessen_parallel_2004}. An other view of our extened |Polish| expression
is a parsing process where results are returned bit by bit.

\citet{swierstra_fast_1999}


\subsection{Summary}


We can summarize the unique points of our approach as follows:

\begin{itemize}
\item
  simple

\item
  no tree update

\item
  taking advantage of lazy evaluation: no startup cost to parse the
  whole file the first time a file is loaded.

\item
  idea is independent of parsing algorithm details (we want an online
  algorithm with error correction)

\item 
  in a parsing combinator library

\end{itemize}
\begin{meta}
What does Visual Haskell do?

\end{meta}



\section{Results}

We carried out development of a parser combinator library for incremental
parsing with support for error correction. We argumented that, using suitable
data structures for the output, the complexity of parsing (without error
correction) is $O(log~m + n)$ where $m$ is the number of tokens in the state we
resume from and $n$ is the number of tokens to parse. Parsing an increment of
constant size has an amortized complexity is $O(1)$.

This paper and accompanying source code has been edited in the Yi editor. The
incremental parser was used to help matching parenthesis and layout the Haskell
functions. Environment delimiters as well as parenthetical
symbols were matched in the \LaTeX source.

\section{Conclusion}
\label{sec:conclusion}


Combination of many techniques to build a working application.

Interesting application for/experiment in lazy evaluation.

\bibliographystyle{mybst}
\bibliography{../Zotero.bib}


\end{document}

% -*- latex -*-
\documentclass[preprint]{sigplanconf}
%include lhs2TeX.fmt
\usepackage{amsmath}
\usepackage[mathletters]{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{graphicx}
\setlength{\parindent}{0pt}
\setlength{\parskip}{6pt plus 2pt minus 1pt}

\usepackage{enumerate}

\begin{document}

\titlebanner{Draft}        % These are ignored unless
\preprintfooter{ICFP09}   % 'preprint' option specified.

\title{Functional Incremental Parsing}

\authorinfo{Jean-Philippe Bernardy}


\maketitle

\begin{abstract}

In the context of an interactive application where the user
observes only a small window of the output (that is, one that
corresponds to a small window of the input), we show that combining
lazy evaluation and caching of intermediate (partial) results
provides incremental parsing. We also introduce a general purpose,
simple data structure, to get rid of the linear complexity caused
by lazy lists traversals while retaining its lazy properties.
Finally, we complete our treatment of incremental parsing in an
interactive system by showing how our parsing machinery can be
improved to support error-correction.
\end{abstract}

\section{Introduction}

\begin{figure}
\includegraphics[width=\columnwidth]{begin}
\label{fig:begin}
\caption{Viewing the beginning of a file. Only the beginning of the file is parsed.}
\end{figure}

\begin{figure}
\includegraphics[width=\columnwidth]{mid}
\label{fig:mid}
\caption{Viewing the beginning of a file.}
\end{figure}


In an interactive system, a lazy evaluation strategy provides a
special form of incremental computation: the amount of output that
is demanded drives the computation to be performed. In other words,
the system responds to incremental movement of the portion of the
output being viewed by the user (window) by incremental computation
of the intermediate structures.

This suggests that we can take advantage of lazy evaluation to
implement incremental parsing for an interactive application.
Indeed, if we suppose that the user makes changes in the input that
``corresponds to'' the window being viewed, it suffices to cache
partially computed results for each point in the input, to obtain a
system that responds to changes in the input independently of the
total size of that input.

In the Yi editor, we used this technique to provide features such
as syntax highlighting and indentation hints for the Haskell
language. The abstract syntax tree (AST) being available at all
times is very convenient to implement all syntax-dependent
functions in a consistent way.

\subsection{Example}

For the purpose of illustration, we will demonstrate how the
technique works on a simple problem: interactive feedback of
parenthesis matching for a lisp-like language. Given an input such
as \verb!(+ 1 (* 5 (+ 3 4)) 2)!, the program will display
\verb!(+ 1 {* 5 [+ 3 4]} 2)!. The idea is that matching pairs are
displayed using different parenthetical symbols for each level,
making the extent of each sub-expression more apparent.

The production of the output is a two-phase process. First, an AST
is produced by parsing the input. Second, and linearizing back the
syntax tree.

The initial situation is depicted in figure 1. The user views the
beginning of the file. To print the decorated output, the program
has to traverse the first few nodes of the syntax tree (in
pre-order). This in turn forces parsing the corresponding part of
the output, but \emph{only so far} (or maybe a few tokens ahead,
depending on the amount of lookahead required).

As the user scrolls down in the file, more and more of the AST is
demanded, and the parsing proceeds in lockstep. (figure 2) If the
user modifies the input at this point, it invalidates the AST, and
therefore we have to re-parse the input. Here, we can again exploit
the linear behaviour of parsing algorithm to our advantage. Indeed,
it we have stored the parser state for the input point where the
user made the modification, we can \emph{resume} parsing from that
point.

\subsection{Contributions}

\begin{itemize}
\item
  We describe a novel implementation of incremental parsing which
  takes advantage of lazy evaluation;

\item
  We craft a data structure to be used in place of lists, which is
  more efficient but has the same properties for laziness;

\item
  We show a complete implementation of a parser combinator library
  for incremental parsing and error correction;

\item
  We have implemented such a system and made use of it to provide
  syntax-dependent feedback in a production-quality editor.

\end{itemize}
\section{Polish Expressions}

In order to represent partially evaluated results, we need a
representation for expressions. Following Swierstra and Hughes, we
use a type with at most one recursive position, giving it a linear
structure. This is necessary to match the linear processing of the
input in parsing algorithms. In contrast to Swierstra however, we
capture the matching of types between functions and arguments in a
GADT, instead of nested types.

\begin{code}
data a :< b
infixr :<

data Steps r where
    Push  :: a -> Steps r                  -> Steps (a :< r)
    App   :: (Steps ((b -> a) :< b :< r))  -> Steps (a :< r)
    Done  ::                                  Steps ()
\end{code}
A value of type |Steps r| can be interpreted as a polish expression
that produces a stack of type |r|.

|Push| produces a stack with one more value than its argument.
|App| transforms the stack produced by its argument: it applies the
function on the top to the argument on the second position. |Done|
produces the empty stack.

It is easy to translate from an applicative language to these
polish expressions, and therefore syntax trees can be outputed in
that form just as easily.

\begin{code}
data Applic a where
    (:*:) :: Applic (b -> a) -> Applic b -> Applic a
    Pure :: a -> Applic a
infixl :*:
toSteps expr = toP expr Done
  where toP :: Applic a -> (Steps r -> Steps (a,r))
        toP (f :*: x)  = App . toP f . toP x
        toP (Pure x)   = Push x
\end{code}
The value of an expression can be evaluated as follows:

\begin{code}
evalR :: Steps (a :< r) -> (a, Steps r)
evalR (Push a r) = (a,r)
evalR (App s) = let (f, s') = evalR s
                    (x, s'') = evalR s'
                in (f x, s'')
\end{code}
\begin{quote}
Note that |fst . evalR . toSteps . traverse = id|.

\end{quote}
\begin{quote}
An alternative, which builds the whole stack (and thus requires a
constructor for :\textless{}) is:

\end{quote}
\begin{code}
evalR :: Steps r -> r
evalR (Push a r) = a :< evalR ss r
evalR (App s) = (\ ~(f:< (a:<r)) -> f a :< r) (evalR ss s)
\end{code}
This evaluation procedure possesses the ``online'' property: parts
of the polish expression are demanded only if the corresponding
parts of the input is demanded. This preserves the incremental
properties of lazy evaluation.

\section{Adding input}

The polish expressions presented so far do not depend on input. We
introduce the |Suspend| constructor to fulfill this role: it
expresses that the rest of the expression can depend on the (first
symbol of) the output. Using this we can extend our applicative
language with a construct to pattern match on the front of the
input, and write a simple parser for valid S-expressions.

\begin{code}
data Steps s r where
    Push   :: a -> Steps s r ->                   Steps s (a :< r)
    App   :: (Steps s ((b -> a) :< b :< r)) ->   Steps s (a :< r)
    Done  ::                                     Steps s ()
    Suspend :: Steps s r -> (s -> Steps s r) ->  Steps s r


data Parser s a where
    (:*:) :: Parser s (b -> a) -> Parser s b -> Parser s a
    Pure :: a -> Parser s a
    Case :: Parser s a -> (s -> Parser s a) -> Parser s a

toP (Case nil cons) = \fut -> Suspend (toP nil fut) (\s -> fromP (toP (cons s) fut))
-- other cases unchanged
\end{code}
\begin{code}
parseList :: Parser Char [SExpr]
parseList = Case 
   (Pure [])
   (\c -> case c of
       ')' -> Pure []
       ' ' -> parseList -- ignore spaces
       '(' -> Pure (\arg rest -> S arg : rest ) :@: parseList :@: parseList
       c -> Pure (Atom c :) :@: parseList)
\end{code}
Suspensions in a polish expression can be resolved by feeding input
into it. When facing a suspension, we pattern match on the input,
and choose the corresponding branch in the result.

\begin{code}
feed :: [s] -> Steps s r -> Steps s r
feed ss p = case p of
                  (Sus nil cons) -> case ss of
                      [] -> feed [] nil
                      Just (s:ss') -> feed (ss') (cons s)
                  (Push x p') -> Push x (feed ss p')
                  (App p') -> App (feed ss p')
\end{code}
\begin{quote}
Hence, |feed "(+ 1 2)" (toSteps parseList)| yields back \ldots{}

\end{quote}
We can also obtain intermediate parsing results by feeding symbols
one at a time. The list of all intermediate results is constructed
lazily using |scanl|.

\begin{code}
feedOne :: Steps s a -> s -> Steps s a
feedOne (Push x s)         ss = Push x (feedOne s ss)
feedOne (App f)            ss = App (feedOne f ss)
feedOne (Suspend nil cons) s  = cons s

partialParses = scanl feedOne
\end{code}
Now, if the $n^{th}$ element of the input is changed, one can reuse
the $n^{th}$ element of the partial results list and feed it the
new input's tail (from that position).

This suffers from a major issue: partial results remain in their
``polish expression form'', and reusing offers almost no benefit,
because no computation is shared beyond construction of the
expression in polish form. Fortunately, it is possible to partially
evaluate prefixes of polish expressions.

The following definition performs this task by performing
applications by traversing the result and applying functions along
the way.

\begin{code}
evalL :: Steps s a -> Steps s a
evalL (Push x r) = Push x (evalL r)
evalL (App f) = case evalL f of
                  (Push a (Push b r)) -> Push (a b) r
                  r -> App r
partialParses = scanl (\c -> evalL . feedOne c)
\end{code}
This still suffers from a major drawback: as long as a function
application is not saturated, the polish expression will start with
a (potentially long) prefix of the form:

\begin{code}
  partialsP = App $ Push v_1 $ App $ Push v_2 $  ... $ App $ Suspend nil cons
\end{code}
which cannot be simplified.

\begin{quote}
after parsing |(abcdefg| we get exactly this.

\end{quote}
This prefix can persist until the end of the input is reached. A
possible remedy is to avoid writing expressions that lead to this
sort of intermediate results, and we will see in section [ref] how
to do this in a particularly important case. This however works
only up to some point: indeed, there must always be an unsaturated
application (otherwise the result would be independent of the
input). In general, after parsing a prefix of size $n$, it is
reasonable to expect a partial application of at least depth
\$O(log\ensuremath{\sim}n), (otherwise the parser discards
information).

Thus we have to use a better strategy to simplify intermediate
results. We want to avoid the cost of traversing the structure
until we find a suspension at each step. This suggests to use a
zipper structure with the focus at this suspension point.

\begin{code}
data Zip output where
   Zip :: RPolish stack output -> Steps stack -> Zip output

data RPolish input output where
  RPush :: a -> RPolish (a :< rest) output -> RPolish rest output
  RApp :: RPolish (b :< rest) output -> RPolish ((a -> b) :< a :< rest) output 
  RStop :: RPolish rest rest
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
an output stack, reverse expressions can be understood as automaton
which transform a stack to another. This is captured in the type
indices |input| and |output|.

In our zipper type, the direct polish expression yet-to-visit
(``on the right'') has to correspond to the reverse polish
automation (``on the left''): the output of the latter has to match
the input of the former.

We capture all these properties in the types by using GADTs. This
allows properly type the traversal of polish expressions as well as
reduction to a value.

\begin{quote}
show the code

\end{quote}
\section{Parsing}

\subsection{Disjunction}

We kept the details of actual parsing out of the discussion so far.
This is for good reason: the machinery for incremental computation
and reuse of partial results is independent from them. Indeed,
given any procedure to compute structured values from a linear
input of symbols, one can use the procedure described above to
transform it into an incremental algorithm.

However, the most common way to produce such structured values is
by \emph{parsing} the input string. To support convenient parsing,
we can introduce a disjunction operator, exactly as Swierstra and
Hughes do: the addition of the |Suspend| operator does not
undermine their treatment of disjunction in any way.

\begin{quote}
The zipper cannot go beyond an unresolved disjunction. That is OK
if we assume that the parser has indeed online behavior.

\end{quote}
\subsection{Error correction}

The online property requires that there is no error in the input.
Indeed, the |evalR| function \emph{must} return a result (we want a
total function!), so the parser must a conjure up a suitable result
for \emph{any} input.

If the grammar is sufficiently permissive, no error correction in
the parsing algorithm itself is necessary. However, most
interesting grammars produce a highly structured result, and are
correspondingly restrictive on the input they accept. Augmenting
the parser with error correction is therefore desirable.

We can do so by introducing an other constructor in the |Steps|
type to represent less desirable parses. The idea is that the
grammar contains permissive rules, but those are tagged as less
desirable. The parsing algorithm can then maximize the desirability
of the set of rules used.

At each disjunction point, the parser will have to choose between
two alternatives. Since we want online behavior, we would like to
do so by looking ahead as few symbols as possible. We introduce a
new type which represents this ``progress'' information. This data
structure is similar to a list where the $n^{th}$ element contains
how much we dislike to take this path after $n$ steps of following
it. The difference is that the list may end with success, failure
or suspension which indicates unknown final result.

If one looks at the tail of the structures, we know exactly how
much the path is desirable. However, as hinted before, we will look
only only a few steps ahead, until we can safely disregard one of
the paths.

In order for this strategy to be efficient, we cache the progress
information in each disjunction node.

This technique can be re-formulated as dynamic programming, where
we use lazy evaluation to automatically cut-off expansion of the
search space. We first define a full tree of possibilities: (Steps
with disjunction), then we compute a profile information that we
tie to it; finally, finding the best path is a matter of looking
only at a subset of the information we constructed, using any
suitable heuristic.

\begin{quote}
Here it's probably best to paste in the whole library.

\end{quote}
\section{Getting rid of linear behavior}

\begin{quote}
This is related to ``Binary random access lists'' in Okasaki.

\end{quote}
As we noted in a previous section, partial computations sometimes
cannot be performed. This is indeed a very common case: if the
output we construct is a list, then the spine of the list can only
be constructed once we get hold of the very tail of it. In
particular, our system will behave very badly for a parser that
returns its input unmodified:

\begin{code}
identity = case_ 
\end{code}
Wagner et al.~recognize this issue and propose to handle the case
of repetition specially in the parsing. We choose a different
approach, which relies on using a different data structure for the
output. The advantage is that we do not need to complicate, not
change at all, the parsing algorithms. The key insight is that the
performance problems come from the linearity of the list, but we
can always use a tree whose structure can be ignored when
traversing the result.

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

\begin{quote}
picture

\end{quote}
A complete tree of total depth $2 d$ can therefore store at least
$\sum_{k=1}^d 2^{k}-1$ elements, fulfilling the second
requirement.

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

There have been a lot of work on incremental interactive algorithm
and applications a long time ago: (Swierstra, Snelting, Wagner et
al), however, these solutions havent caught up in the mainstream.
Editors typically work using regular expressions for syntax
highlighting at the lexical level (Emacs, Vim, Textmate, \ldots{})
or run a full compiler in the background for syntax level
(Eclipse). We might argue that these solutions offered little
benefit in comparison to their implementation cost. Our approach is
much simpler. In particular, most imperative-oriented approaches
try to update the tree as the user changes the text. This is a lot
more complicated than what we do. One might argue that update of
the tree

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

\end{itemize}
\begin{quote}
What does Visual Haskell do?

\end{quote}
\section{Results}

We carried out development of a parser combinator library for
incremental parsing with support for error correction. We
argumented that the complexity of the parsing is linear, and that
is can cost

\begin{quote}
The full code is in Code.hs

\end{quote}
\end{document}

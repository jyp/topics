% -*- latex -*-
\documentclass[preprint]{sigplanconf}
%include lhs2TeX.fmt
%format :*: = " \applbind"
\usepackage{amsmath}
\usepackage[mathletters]{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{graphicx}
% \setlength{\parindent}{0pt}
% \setlength{\parskip}{6pt plus 2pt minus 1pt}
\usepackage{enumerate}
\usepackage[sort&compress,numbers]{natbib}

\providecommand{\TODO}[1]{\footnote{#1}}
\providecommand{\annot}[1]{\marginpar{\footnotesize \raggedright #1}}
\newcommand{\applbind}{\mathbin{:\!\!*\!\!:}}

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

\title{Functional Incremental Parsing}

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
Finally, we complete our treatment \annot{better word?} of incremental parsing in an
interactive system by showing how our parsing machinery can be
improved to support error-correction.
\end{abstract}

\category{D.3.4}{Programming Languages}: Processors
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

\begin{code}
data SExpr = S [SExpr] | Atom Char
\end{code}


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
\label{fig:mid}

\caption{
Viewing the middle of a file. 
Although only a small amount of the
parse tree may be demanded, parsing must start from the beginning of the
file.}

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

\begin{meta}
    Roadmap for the paper
\end{meta}

The rest of the paper will describe how to build the parsing library step by
step: production of results in a online way, map the input to these results and
manage the incremental computation of intermediate state, treat disjunction and
error correction. We discuss related work in section \ref{sec:relatedWork} and
conclude in section \ref{sec:conclusion}.

\section{Producing results} 
\label{sec:applicative}

In this section we concentrate on constructing parsing results, ignoring the
dependence on input. The cornerstone of our approach to incremental parsing
approach is that the parse tree is produced \emph{online}. We can ensure that
this is the case by forcing the structure of the result to be expressed in
applicative \citet{mcbride_applicative_2007} form.


The following data type captures the pure applicative language with embedding
of Haskell values. It is indexed by the type of values it represents.

\begin{code}
data Applic a where
    (:*:) :: Applic (b -> a) -> Applic b -> Applic a
    Pure :: a -> Applic a
infixl :*:
\end{code}

The idea is to reify function applications.

For example, the Haskell expression |S [Atom'a']|, which stands for |S ((:)
(Atom 'a') [])| if we remove syntactic sugar, can be represented in applicative
form by

\begin{code}
S @ ((:) @ (Atom @ 'a') @ [])
\end{code}

Or, using our datatype:

\begin{code}
Pure S :*: (Pure (:) :*: (Pure Atom :*: Pure 'a') :*: Pure [])
\end{code}

We can evaluate such expressions as follows:

\begin{code}
evalA (f :*: x) = (evalA f) (evalA x)
evalA (Pure a) = a
\end{code}

If the arguments to the |Pure| constructor are constants \annot{or
constructors}, then we know that demanding a given part of the result will force
only the corresponding part of the applicative expression.

Because they process the input in a linear fashion, our parsers require a
linear structure (it will become apparent in section~\ref{sec:parsing}). As
\citet{hughes_polish_2003}, we convert the applicative expressions to polish
representation to obtain such a linear structure.

The key idea of the polish representation is to put the application in an
prefix position rather than an infix one.

Hence our example expression in applicative form
|S @ ((:) @ (Atom @ 'a') @ [])|
becomes
|@ S @ (@ (:) (@ Atom 'a') [])|

The parenthesis are no longer needed, since we know that |@| is always followed
by exactly two arguments. The final polish expression is therefore

\begin{code}
 S @ @ (:) @ Atom 'a' []
\end{code}

or, sticking to pure haskell syntax:
\begin{code}
App $ Push S $ App $ App $ Push (:) $ App $ Push Atom $ Push 'a' $ Push [] $ Done
\end{code}

Typing these expressions in Haskell is somewhat tricky. The key insight is that
polish expressions are in fact more general than applicative expressions: they
produce a stack of values instead of just one.

In extenso, |Push| produces a stack with one more value than its argument,
|App| transforms the stack produced by its argument by applying the function on
the top to the argument on the second position, and |Done| produces the empty
stack.

The expression |Push (:) $ App $ Push Atom $ Push 'a' $ Push [] $ Done| is an
example producing a non-trivial stack. It produces the stack |(:) (Atom 'a')
[]|, which can be expressed purely in Haskell as |(:) :< Atom 'a' :< [] :< Nil|,
using the following representation for heterogeneous stacks.

\begin{code}
data top :< rest = (:<) {top :: top, rest :: rest}
data Nil = Nil
infixr :<
\end{code}

We are now able to properly type polish expressions, by indexing the datatype
with the type of the stack produced.

\begin{code}
data Polish r where
    Push  :: a -> Polish r                  ->  Polish (a :< r)
    App   :: (Polish ((b -> a) :< b :< r))  ->  Polish (a :< r)
    Done  ::                                    Polish Nil
\end{code}

We can now write a translation from the pure applicative language to
polish expressions.

\begin{code}
toPolish :: Applic a -> Polish (a :< Nil)
toPolish expr = toP expr Done
  where toP :: Applic a -> (Polish r -> Polish (a,r))
        toP (f :*: x)  = App . toP f . toP x
        toP (Pure x)   = Push x
\end{code}

And the value of an expression can be evaluated as follows:

\begin{code}
evalR :: Steps r -> r
evalR (Val a r) = push a (evalR r)
evalR (App s) = apply (evalR s)
    where  apply  ~(f:< ~(a:<r))  = f a :< r
           push  a                = (a :<)
\end{code}

% evalR :: Polish (a :< r) -> (a, Polish r)
% evalR (Push a r) = (a,r)
% evalR (App s) =  let  (f, s') = evalR s
%                       (x, s'') = evalR s'
%                  in (f x, s'')

We have the equality |top (evalR (toPolish x)) == evalA x|.

Finally, we note that this evaluation procedure still possesses the ``online''
property: parts of the polish expression are demanded only if the corresponding
parts of the input is demanded. This preserves the incremental properties of
lazy evaluation. In fact, the equality above holds even when |undefined| appears
as argument to the |Pure| constructor.

In fact, the conversion from applicative to polish expressions can be seen as 
a reification of the working stack of the |evalA| function with call-by-name
semantics.


\section{Adding input}
\label{sec:input}

While studying the pure applicative language is interesting in its
own right (we come back to it later for the Zipper), it is not enough
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

Using just this we can write a simple parser for valid
S-expressions.

\begin{code}
parseList :: Parser Char [SExpr]
parseList = Case 
   (Pure [])
   (\c -> case c of
       ')' -> Pure []
       ' ' -> parseList -- ignore spaces
       '(' -> Pure (\arg rest -> S arg : rest ) :*: parseList :*: parseList
       c -> Pure (Atom c :) :*: parseList)
\end{code}


We introduce the corresponding construct in the |Polish| expressions and amend
the translation.

\begin{code}
data Polish s r where
    Push     :: a -> Polish s r ->                   Polish s (a :< r)
    App      :: (Polish s ((b -> a) :< b :< r)) ->   Polish s (a :< r)
    Done     ::                                      Polish s Nil
    Susp  :: Polish s r -> (s -> Polish s r) ->   Polish s r

  toP (Case nil cons) = 
       \k -> Susp (toP nil k) (\s -> fromP (toP (cons s) k))
  ... ( other cases unchanged)
\end{code}

We broke the linearity of the type, but it does not matter since the
parsing algorithm will not proceed further than the available input anyway. When
the input is available, it is first used to remove the |Susp| constructors.

Suspensions in a polish expression can be resolved by feeding input
into it. When facing a suspension, we pattern match on the input,
and choose the corresponding branch in the result.

\begin{code}
feed :: [s] -> Polish s r -> Polish s r
feed ss p = case p of
                  (Sus nil cons) -> case ss of
                      [] -> feed [] nil
                      Just (s:ss') -> feed (ss') (cons s)
                  (Push x p') -> Push x (feed ss p')
                  (App p') -> App (feed ss p')
\end{code}
\begin{meta}
Hence, |feed "(+ 1 2)" (toPolish parseList)| yields back \ldots{}

\end{meta}
We can also obtain intermediate parsing results by feeding symbols
one at a time. The list of all intermediate results is constructed
lazily using |scanl|.

\begin{code}
feedOne :: Polish s a -> s -> Polish s a
feedOne (Push x s)         ss = Push x (feedOne s ss)
feedOne (App f)            ss = App (feedOne f ss)
feedOne (Susp nil cons) s  = cons s

partialParses = scanl feedOne
\end{code}
Now, if the $(n+1)^{th}$ element of the input is changed, one can reuse
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
evalL :: Polish s a -> Polish s a
evalL (Push x r) = Push x (evalL r)
evalL (App f) = case evalL f of
                  (Push a (Push b r)) -> Push (a b) r
                  r -> App r
partialParses = scanl (\c -> evalL . feedOne c)
\end{code}
This still suffers from a major drawback: as long as a function
application is not saturated, the polish expression will start with

For example, after applying the s-expr parser to the string `(abcdefg`,
evalL is unable to perform any simplification of the list prefix.

\begin{code}
evalL $ feed "(abc" (toPolish parseList) 
  == App $ Push (Atom 'a' :) $ App $ Push (Atom 'b' :) $ App $ Push (Atom 'b' :) $ App $ ...
\end{code}

This prefix can persist until the end of the input is reached. A
possible remedy is to avoid writing expressions that lead to this
sort of intermediate results, and we will see in section~\ref{tree_struc} how
to do this in the particularly important case of lists. This however works
only up to some point: indeed, there must always be an unsaturated
application (otherwise the result would be independent of the
input). In general, after parsing a prefix of size $n$, it is
reasonable to expect a partial application of at least depth
$O(log~n)$, (otherwise the parser discards
information).

\subsection{Zipping into Polish}

Thus we have to use a better strategy to simplify intermediate
results. We want to avoid the cost of traversing the structure
until we find a suspension at each step. This suggests to use a
zipper structure with the focus at this suspension point.

\begin{code}
data Zip output where
   Zip :: RPolish stack output -> Polish stack -> Zip output

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
an output stack, reverse expressions can be understood as an automaton
which transforms a stack to another. This is captured in the type
indices |input| and |output|.

Running this automaton on an input stack offers no surprise.
\begin{code}
evalRP :: RPolish input output -> input -> output
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
right :: Zip s output -> Zip s output
right (Zip l (Push a r)) = Zip (RPush a l) r
right (Zip l (App r)) = Zip (RApp l) r
right (Zip l s) = (Zip l s)
\end{code}

As the input is traversed, we also simplify the prefix that
we went past.
\begin{meta}
Note that this works only because we keep the automaton in "normal form"

\end{meta}

\begin{code}
simplify :: RPolish s output -> RPolish s output
simplify (RPush a (RPush f (RApp r))) = simplify (RPush (f a) r)
simplify x = x
\end{code}

\textmeta{As the polish representation corresponds to call-by-name evaluation,
reverse polish corresponds to call-by-value.}

\section{Parsing}
\label{sec:parsing}
\textmeta{Termination if there is no recursive call before parsing one token}
\subsection{Disjunction}

We kept the details of actual parsing out of the discussion so far.
This is for good reason: the machinery for incremental computation
and reuse of partial results is independent from them. Indeed,
given any procedure to compute structured values from a linear
input of symbols, one can use the procedure described above to
transform it into an incremental algorithm.

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

The online property requires that there is no error in the input.
Indeed, the |evalR| function \emph{must} return a result (we want a
total function!), so the parser must a conjure up a suitable result
for \emph{any} input.

If the grammar is sufficiently permissive, no error correction in the parsing
algorithm itself is necessary. This was the case for our simple s-expression parser.
However, most interesting grammars produce a highly structured result, and are
correspondingly restrictive on the input they accept. Augmenting the parser with
error correction is therefore desirable.

We can do so by introducing an other constructor in the |Parser| type to denote
less desirable parses. The intent is to extend the grammar with permissive rules
for recovering errors, tagging those as less desirable. The parsing algorithm
can then maximize the desirability of the set of rules used for parsing a given
fragment of input.

\begin{code}
data Parser s a where
    Pure :: a -> Parser s a
    (:*:) :: Parser s (b -> a) -> Parser s b -> Parser s a
    Case :: Parser s a -> (s -> Parser s a) -> Parser s a
    Disj :: Parser s a -> Parser s a -> Parser s a
    Yuck :: Parser s a -> Parser s a
\end{code}

At each disjunction point, the evaluation function will have to choose between
two alternatives. Since we want online behavior, we cannot afford to look
further than a few symbols ahead to decide which parse might be the best.
(Additionally the number of potential recovery paths grows exponentially with
the amount of lookahead). We use widespread technique to thin out search after 
some constant, small amount of lookahead.

In contrast to \citep{hughes_polish_2003}, we do not compute the best path by
direct manipulation of the polish representation. Instead, we introduce a new
datatype which represents the ``progress'' information only.

\begin{code}
data Progress = PSusp | PRes Int | !Int :> Progress
\end{code}
\textmeta{We can't really use |fix Dislike|, because we use strict Ints.}

This data structure is similar to a list where the $n^{th}$ element contains
how much we dislike to take this path after shifting $n$ symbols following it.
The difference is that the list may end with success or suspension,
depending on wheter the parser reached the end of the input or not.

Given two (terminated) |Progress| values, it is possible to determine which is
best to take by demanding only a prefix of each (as long as the grammar is not
ambiguous).

We can now use this information to determinte which path to take when facing a
disjunction. In turn, this allows to compute the progress information on the
basis of the polish representation only.


\begin{figure}
\begin{code}
data Polish s a where
    Push   :: a -> Polish s r                      -> Polish s (a :< r)
    App   :: Polish s ((b -> a) :< (b :< r))      -> Polish s (a :< r)
    Done  ::                               Polish s ()
    Shift ::           Polish s a        -> Polish s a
    Sus :: Polish s a -> (s -> Polish s a) -> Polish s a
    Best :: Ordering -> Progress -> Polish s a -> Polish s a -> Polish s a
    Dislike :: Polish s a -> Polish s a

progress :: Polish s r -> Progress
progress (Push _ p) = progress p
progress (App p) = progress p
progress (Shift p) = 0 :> progress p
progress (Done) = PRes 0 -- success with zero dislikes
progress (Dislike p) = mapSucc (progress p)
progress (Sus _ _) = PSusp
progress (Best _ pr _ _) = pr

toP (Case a f) = \fut -> Sus (toP a fut) (\s -> toP (f s) fut)
toP (f :*: x) = App . toP f . toP x
toP (Pure x)   = Push x
toP (Disj a b)  = \fut -> mkBest (toP a fut) (toP b fut)
toP (Yuck p) = Dislike . toP p 

mkBest :: Polish s a -> Polish s a -> Polish s a
mkBest p q = let ~(choice, pr) = better 0 (progress p) (progress q) in Best choice pr p q

better :: Progress -> Progress -> (Ordering, Progress)
...
\end{code}
\caption{Handling disjunction}
\end{figure}

Proceeding exactly as such is horribly inefficient, but we can use the classic
trick \cite{swierstra} to cache the progress information in the |Polish|
representation.

Here, we finally see why the |Polish| representation is so important:
the progress information cannot be associated to a |Parser|, because
it may depend on whatever parser \emph{follows} it. This is not
an issue in the |Polish| representation, because it is unfolded until
the end of the parsing.


The technique can be re-formulated as lazy dynamic programming
\citet{allison_lazy_1992}. We first define a full tree of possibilities: (Polish
with disjunction), then we compute a profile information that we tie to it;
finally, finding the best path is a matter of looking only at a subset of the
information we constructed, using any suitable heuristic. Our cut-off heuristic
makes sure that only a part of the exponentially big data structure is demanded.
Thanks to lazy evaluation, only that small will be actually constructed.

\subsection{Ambiguous grammars}

\textmeta{Conflict with online; solved as by error correction}

\section{Eliminating linear behavior}
\label{sec:sublinear}

\begin{meta}

This is related to ``Binary random access lists'' in
\citet[section~6.2.1]{okasaki_purely_1999}. \end{meta}

As we noted in a previous section, partial computations sometimes
cannot be performed. This is indeed a very common case: if the
output we construct is a list, then the spine of the list can only
be constructed once we get hold of the very tail of it. In
particular, our system will behave very badly for a parser that
returns its input unmodified:

\begin{code}
identity = case_ 
\end{code}

The key insight is that the performance problems come from the linearity of the
list, but we can always use a tree whose structure can be ignored when
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

\begin{meta}
picture

\end{meta}
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


Despite extensive research dating back as far as 30 years ago, somehow, none of
these solutions have caught up in the mainstream.
Editors typically work using regular expressions for syntax
highlighting at the lexical level (Emacs, Vim, Textmate, \ldots{})
or run a full compiler in the background for syntax level
(Eclipse). 

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
possible prefix.}

\subsection{Incremental parsing in natural language processing} 

\textmeta{Krasimir}

\subsection{Incremental computation}

\citet{saraiva_functional_2000}

An alternative approach would be to build the system on top of a generic
incremental computation system. Downsides are that there currently exists no
such off-the-shelf system for Haskell. The closest matching solution is provided
by \citet{carlsson_monads_2002} relies heavily on explicit threading of
computation through monads and explict reference for storage of inputs or
intermediate results. In our case, not only the contents of the inputs will change, but also their number.



\subsection{Parser combinators}

Our approach is in the tradition of parser combinator libraries, in
particular as described by \citet{hughes_polish_2003}.
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

We carried out development of a parser combinator library for
incremental parsing with support for error correction. We
argumented that the complexity of the parsing is linear, and that
is can cost

\section{Conclusion}
\label{sec:conclusion}

\textmeta{Discuss how the tree must be used only locally}

Combination of many techniques to build a working application.

Interesting application for/experiment in lazy evaluation.

\bibliographystyle{mybst}
\bibliography{../Zotero.bib}


\end{document}

% -*- latex -*-
\documentclass[preprint]{sigplanconf}
%include lhs2TeX.fmt
%format :*: = " \applbind"
%format :|: = " \disjunct"
%format +> = " \secondPush"
\usepackage{amsmath}
\usepackage[mathletters]{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{graphicx}
\usepackage{pgf}
\usepackage{tikz}
\usetikzlibrary{trees,positioning,arrows}
\setlength{\parindent}{0pt}
\setlength{\parskip}{3pt}
\usepackage{enumerate}
% \usepackage[sort&compress,numbers]{natbib}
\usepackage[sort&compress]{natbib}
\usepackage{url}
\newcommand{\ignore}[1]{}
\providecommand{\TODO}[1]{\footnote{#1}}
\providecommand{\annot}[1]{\marginpar{\footnotesize \raggedright #1}}
\newcommand{\applbind}{\mathbin{:\!\!*\!\!:}}
\newcommand{\disjunct}{\mathbin{:\!\!||\!\!:}}
\newcommand{\secondPush}{\mathbin{+\!\!>}}
\newcommand{\prog}{\ensuremath{\mathbin{:>}}}

\newenvironment{meta}{%
\begin{quote}
\sf
}{%
\end{quote}
}

\providecommand{\textmeta}[1]{\begin{quote}\textsf{{#1}}\end{quote}}
\newcommand{\comment}[1]{}

\begin{document}

\titlebanner{Draft}        % These are ignored unless
\preprintfooter{In preparation for ICFP09}   % 'preprint' option specified.

\title{Lazy Functional Incremental Parsing}

\authorinfo{Jean-Philippe Bernardy}
           {Computer Science and Engineering, 
            Chalmers University of Technology and University of Gothenburg}
           {bernardy@@chalmers.se}


\maketitle

\comment{Make sure online and incremental parsing are well defined.}
\textmeta{Use arithmetic expressions as an example}

\begin{abstract}

Structured documents are commonly edited using a free-form editor. 
Despite the editor accepting all inputs, It makes sense to maintain a structured
representation of the edited document. The structured representation has a number of uses:
structural navigation (and optional structural edition), structure highlighting, etc. 
The construction of the structure must be done incrementally to be
efficient: the time to process an edit operation should be proportional to the
size of the change, and (ideally) independent of the total size of the document.

We show that combining
lazy evaluation and caching of intermediate (partial) results
enables incremental parsing. % to parse the input incrementally. 
% This is crap!
% We also introduce a simple general purpose data structure, to eliminate the linear complexity caused by lazy lists traversals while retaining their lazy properties.
We build a complete incremental parsing library for
interactive systems with support for error-correction.
\end{abstract}

\category{D.3.4}{Programming Languages}{Processors}
\category{D.2.3}{Coding Tools and Techniques}{Program editors}
\category{D.1.1}{Programming Techniques}{Applicative (Functional) Programming}
\category{F.3.2}{Logics and Meanings of Programs}{Semantics of Programming Languages}

\terms
Algorithms, Languages, Design, Performance, Theory

\keywords
% Functional Programming, 
Lazy evaluation, Incremental Computing, Parsing,
Dynamic Programming, Polish representation, Editor, Haskell


\section{Introduction}



\begin{figure}
\includegraphics[width=\columnwidth]{yi-ghc-simplifier}
\caption{Screenshot. The user has opened a very big Haskell file. Yi
  gives feedback on matching parenthesis by changing the background
  color. 
%   Some parenthesis do not match because of the layout rule: the
%   closing ones should be indented. Yi understands that and shows them
%   in a different color.
  Despite the file being very big, the feedback can be given
  as the user types, because parsing is performed incrementally.
}
\label{fig:screenshot}
\end{figure}


Yi \citep{bernardy_yi:editor_2008,stewart_dynamic_2005} is a text editor
written in Haskell. It provides features such as syntax highlighting and
indentation hints for a number of programming languages (figure
\ref{fig:screenshot}). 
All syntax-dependent functions rely on the abstract syntax tree (AST) of the
source code being available at all times. The feedback given by the editor is
always consistent with the text: the AST is kept up to date after each
modification. But, to maintain acceptable performance, the editor must not parse
the whole file at each keystroke: we have to implement a form of incremental
parsing.

Another feature of Yi is that it is configurable in Haskell. Therefore, we
prefer to use the Haskell language for every aspect of the application, so that
the user can configure it. In particular, syntax should be described using a
combinator library.

Our main goals can be formulated as constraints on the parsing library:
\begin{itemize}
\item it must be programmable through a combinator interface;
\item it must cope with all inputs provided by the user, and thus provide error correction;
\item it must be efficient enough for interactive usage: parsing must be done incrementally.
\end{itemize}

To implement this last point, one could choose a stateful approach and update the parse tree as the user
modifies the input structure. Instead, in this paper we explore the possibility to use a
more ``functional'' approach: we minimize the amount of state that has to be updated,
and rely on laziness to implement incrementality as much as possible.

\subsection{Approach}

In this section we sketch how laziness can help achieving incremental parsing.

An \emph{online} parser exhibits lazy behavior: it does not proceed further 
than necessary to return the nodes of the AST that are demanded.


\begin{figure}
\includegraphics[width=\columnwidth]{begin}
\caption{Viewing the beginning of a file. 
The big triangle represents the syntax tree. The line at the bottom represents the
file. The zagged part indicates the part that is parsed. The viewing window is
depicted as a rectangle.
}
\label{fig:begin}
\end{figure}

Assume that, in addition to using an online parser to produce the AST, it is traversed
in pre-order to display the decorated text presented to the user.
Then, the situation right after opening a file is depicted in figure~\ref{fig:begin}. The window is positioned
at the beginning of the file. To display the decorated output, the program
has to traverse the first few nodes of the syntax tree (in
pre-order). This in turn forces parsing the corresponding part of
the input, but, thanks to lazy evaluation, \emph{only so far} (or maybe a few tokens ahead,
depending on the amount of look-ahead required). If the user modifies
the input at this point, it invalidates the AST, but discarding it and
re-parsing is not too costly: only a screenful of parsing needs to be
re-done.

\begin{figure}
\includegraphics[width=\columnwidth]{mid}
\caption{
Viewing the middle of a file.
Parsing proceeds in linear fashion:  
although only a small amount of the
parse tree may be demanded, it will depend not only on the portion of the input that corresponds to it, but also 
on everything that precedes.
}
\label{fig:mid}
\end{figure}

As the user scrolls down in the file, more and more of the AST is demanded, and
the parsing proceeds in lockstep (figure~\ref{fig:mid}). 
At this stage, a user modification is more
serious: re-parsing naively from the beginning can be too costly for a big file.
Fortunately we can again exploit the linear behavior of parsing algorithms to
our advantage. Indeed, if we have stored the parser state for the input point
where the user made the modification, we can \emph{resume} parsing from that
point. If we make sure to store partial results for every point of the input, we
can ensure that we will never parse more than a screenful at a time. Thereby, we
achieve incremental parsing, in the sense that the amount of parsing work needed
after each user interaction is constant.



\subsection{Contributions}

Our contributions can be summarized as follows.

\begin{itemize}
\item
  We describe a novel, purely functional approach to incremental parsing, which
  makes essential use of lazy evaluation. This is achieved by
  combining online parsers with caching of intermediate
  results.

\item
  We complete our treatment of incremental parsing with 
  error correction. This is essential, since online parsers
  need to be \emph{total}: they cannot fail on any input;

\ignore{
\item
  We craft a data structure to be used in place of lists, which is
  more efficient but has the same properties for laziness;
}

\item
  We have implemented such a system in a parser-combinator library;

\item
  We made use of it to provide syntax-dependent feedback in a production-quality editor.

\end{itemize}

\subsection{Interface and Outlook}

\label{sec:interface}

Our goal is to provide a combinator library with a standard interface, similar to that
presented by \citet{swierstra_combinator_2000}.

Such an interface can be captured in a generalized algebraic data type (GADT)
as follows. These combinators are traditionally given as functions instead of
constructors but since we make extensive use of GADTs for modeling purposes at
various levels, we prefer to use this presentation style everywhere for
consistency.

\begin{spec}
data Parser s a where
    Pure   :: a                                  ->  Parser s a
    (:*:)  :: Parser s (b -> a) -> Parser s b    ->  Parser s a
    Symb   :: Parser s a -> (s -> Parser s a)    ->  Parser s a
    Disj   :: Parser s a -> Parser s a           ->  Parser s a
    Fail   ::                                        Parser s a
\end{spec}

This interface supports production of results (|Pure|), sequencing (|:*:|)
reading of input symbols (|Symb|), and disjunction (|Disj|, |Fail|).


Most of this paper is devoted to uncover an appropriate representation for our
parsing process type, and the implementation of the functions manipulating it.
The core of this representation is introduced in section~\ref{sec:applicative},
where we merely handle the |Pure| and |:*:| constructors. Dependence on input
and the constructor |Symb| are treated in section~\ref{sec:input}. Disjunction
and error correction will be implemented as a refinement of these concepts in
section~\ref{sec:parsing}.

Parsing combinator libraries usually propose a mere
|run| function that executes the parser on a given input: |run :: Parser s a ->
[s] -> [a]|. 
Incremental systems requires finer control over the execution of the parser.
Therefore, we have to split the |run| function into pieces and reify the parser
state in values of type |Process|.

% We propose the following types:
% 
% \begin{itemize}
%  \item |Parser :: * -> * -> *|: The type of parser descriptions. Is is parametrized by token type and parsing result.
%  \item |Process :: * -> * -> *|: The type of parser states, parametrized as |Parser|.
% \end{itemize}

We also need a few functions to create and manipulate the parsing processes:

\begin{itemize}
 
 \item |mkProcess :: Parser s a -> Process s a|: given a parser description, create the corresponding initial parsing process.
 \item |feed :: [s] -> Process s a -> Process s a|: feed the parsing process with a number of symbols.
 \item |feedEof :: Process s a -> Process s a|: feed the parsing process with the end of the input.
 \item |precompute :: Process s a -> Process s a|: transform a parsing process by pre-computing all the intermediate parsing results available.
 \item |finish :: Process s a -> a|: compute the final result of the parsing, in an online way. This assumes that the end of input has been fed into the process.
\end{itemize}

Section \ref{sec:mainloop} details our approach to incrementality by sketching
the main loop of an editor using the above interface.
The implementation for these functions can be given 
as soon as we introduce
dependence on input in section~\ref{sec:input}.

Sections \ref{sec:applicative} through
\ref{sec:parsing} describe our parsing machinery is built, step by step.
In section~\ref{sec:sublinear} we discuss the problem of incremental parsing of
the repetition construct. We discuss and compare our approach to alternatives in
section~\ref{sec:relatedWork} through section~\ref{sec:results} and conclude in section \ref{sec:conclusion}.

%include Full.lhs
%include Applicative.lhs
%include Input.lhs
%include Choice.lhs
%include Sublinear.lhs

\section{Related work}
\label{sec:relatedWork}

The literature on analysis of programs, incremental or not, is so abundant
that a complete survey would deserve its own treatment. Here we will compare our
approach to some of the closest alternatives.

\subsection{Development environments} 


The idea of incremental analysis of programs is not new.
\citet{wilcox_design_1976} already implemented such a system. The program would
work very similarly to ours: parsing states to the left of the cursor were saved
so that changes to the program would not force a complete re-parse. A big
difference is that it would not rely on built-in lazy evaluation: the online production
of ``results'' would have to be managed entirely by hand. It also did not
provide error correction nor analysis to the right of the cursor.


\citet{ghezzi_incremental_1979} 
% and \citet{ghezzi_augmenting_1980}
improved the concept by also reusing parsing results to the right of the cursor:
after parsing every symbol they check if the new state of the LR automaton
matches that of the previous run. If it does they know they can reuse the
results from that point on. 

This improvement offers some advantages over \citet{wilcox_design_1976} which
still apply when compared to our solution.

\begin{enumerate} 
\item If the user jumps back and forth between the beginning and the end of the
file, every forward jump will force re-parsing the whole file. Note that we
mitigate this drawback in our system by caching the (lazily constructed)
whole parse tree: a full re-parse is required only when the user makes a change
while viewing the beginning of the file.

\item Another advantage is that the AST is fully constructed at all times.
In our case only the part to the left of the window is available.
This means that the functions that traverse the AST should do
so in pre-order. If this is not the case, the online property becomes
useless. For example, if one wishes to apply a sorting algorithm before
displaying an output, this will force the whole input to be parsed before
displaying the first element of the input. In particular, the arguments to the
|Pure| constructor must not perform such operations on its arguments. Ideally,
they should be simple constructors. This leaves many risks for the user of
the library to destroy its incremental properties.
\end{enumerate}

While our approach is much more modest, it is better in some respects.

\begin{enumerate}
\item One benefit of not analyzing the part of the input to the right of the cursor
is that there is no start-up cost: only a screenful of text needs to be parsed
to start displaying it.

\item Another important point is that a small change in the input may often
completely invalidate the results from the previous parsing runs. 
A simple example is the opening of a comment. (For example,
while editing an Haskell source file, typing \verb!{-! implies that the rest of
the file becomes a comment up to the next \verb!-}!.)

It is therefore questionable that reusing right-bound parts of the parse
tree offers any reasonable benefit in practice: it seems to be optimizing for a
special case. This is not very suitable in an interactive system where users
expect consistent response times.

\item Finally, comparing parser states is very tricky to accomplish in the
context of a combinator library: since parsing states normally contain
abstractions, it is not clear how they can be compared to one another.
\end{enumerate}

Later, \citet{wagner_efficient_1998} improved on the state-matching technique.
They contributed the first incremental parser that took in account the
inefficiency of linear repetition. We compared our approach to theirs in
section~\ref{sec:sublinear}.

Despite extensive research dating as far back as 30 years ago, somehow, none of
these solutions have caught up in the mainstream. Editors typically work using
regular expressions for syntax highlighting at the lexical level (Emacs, Vim,
Textmate, \ldots{}) and integrated development environments run a full compiler
in the background for syntax level feedback (Eclipse).
\begin{meta}
What does Visual Haskell do?
\end{meta}

It is possible that the implementation cost of earlier solutions outweighed
their benefits. We hope that the simplicity of our approach will permit more
widespread application.


% \subsection{Incremental parsing in natural language processing} 
% 
% 
% In natural language processing, a parsing alagorithm is deemed incremental if ``it
% reads the input one token at a time and calculates all the possible consequences
% of the token, before the net token is read.''
% 
% We note that there is no notion of AST update in this definition.
% 
% \comment{Does this correspond to the online property or the other?}

\subsection{Incremental computation}

An alternative approach would be to build the library as a plain parser on top
of a generic incremental computation system. The main drawback is that there
currently exists no such off-the-shelf system for Haskell. The closest
matching solution is provided by \citet{carlsson_monads_2002}, and relies
heavily on explicit threading of computation through monads and explicit
reference for storage of inputs and intermediate results. This imposes an
imperative description of the incremental algorithm, which does not match our
goals. Furthermore, in the case of parsing, the inputs would be the individual
symbols. This means that, not only their contents will change from one run to
another, but their numbers will as well. One then might want to rely on laziness,
as we do, to avoid depending unnecessarily on the tail of the input, but then we
hit the problem that the algorithm must be described imperatively.
Therefore, we think that such an approach would be awkward, if at all applicable.

\subsection{Parser combinators}

Our approach is firmly anchored in the tradition of parser combinator libraries
\citep{hutton_monadic_1998}, and particularly close to the polish parsers of
\citet{hughes_polish_2003}.

The introduction of the |Susp| operator is directly inspired by the parallel
parsing processes of \citet{claessen_parallel_2004}, which features a very similar
construct to access the first symbol of the input and make it accessible to
the rest of the computation. This paper presents our implementation as a version of
polish parsers extended with an evaluation procedure ``by-value'', but we could
equally have started with parallel parsing processes and extended them with
``by-name'' evaluation. The combination of both evaluation techniques is unique
to our library.

While error correction mechanism was developed independently, it bears many
similarities with that presented by \citet{swierstra_fast_1999}: they also
associate some variant of progress information to parsers and rely on thinning
and laziness to explore the tree of all possible parses.


\section{Discussion}


Due to our choice to commit to a purely functional, lazy approach, our 
incremental parsing library occupies a unique point in the design space.

More specifically, it is the first time an incremental parsing system
is implemented in a combinator library.

\textmeta{pro and con of using laziness. where do we use laziness? where are we forced to be careful because of that?
Big advantage: the users of the tree are decoupled from their producers.
Big disadvantage: the users should be careful not to break laziness.
}


\section{Future work}

Our treatment of repetition is stull lacking: we would like to retrieve any
node by its position in the input while preserving all properties of laziness
intact. While this might be very difficult to do in the general case, we expect
that our zipper structure can be used to guide the retrieval of the element at
the current point of focus, so that it can be done efficiently.

Although it is trivial to add a \emph{failure} combinator to the library
presented here, we refrained from doing so because it can lead to failing
parsers. However, in practice this can most often be emulated by a repetitive
usage of the |Yuck| combinator. This can lead to some performance loss, as
the ``very disliked'' branch would require more analysis to be discarded than an
immediate failure. Indeed, if one takes this idea to the extreme and tries to
use the fix-point (|fix Yuck|) to represent failure, it will lead to
non-termination. This is due to our use of strict integers in the progress
information. We have chosen this representation to emphasize the dynamic
programming aspect of our solution, but in general it might be more efficient to
represent progress by a mere interleaving of |Shift| and |Dislike| constructors.

Our library suffers from the usual drawbacks of parser combinator approaches.
In particular, it is impossible to write left-recursive parsers, because they
yield a non-terminating loop in the parsing algorithm. We could proceed as
\citet{baars_typed_2009} and represent the grammar rules and transform them on
the fly. It is interesting to note however that we could represent traditional
left-recursive parsers as long as they either consume or \emph{produce} data,
provided the progress information is indexed by the number of |Push|es in
addition to |Shift|s.

Finally, we might want to re-use the right hand side of previous parses. This could
be done by keeping the parsing results \emph{for all possible prefixes}. Proceeding
in this fashion would avoid the chaotic situation where a small modification might
invalidate all the parsing work that follows it, since we take in account \emph{all}
possible prefixes ahead of time.


\comment{
Plugging an attribute evaluator on top of this?
This does not really work since we do not reuse the result. 
\citet{saraiva_functional_2000}

We could put a semantic layer by replacing the constructors with arbitrary
semantic functions. Incrementality is not guaranteed then.
}



\section{Results}
\label{sec:results}

We carried out development of a parser combinator library for incremental
parsing with support for error correction. We argumented that, using suitable
data structures for the output, the complexity of parsing (without error
correction) is $O(log~m + n)$ where $m$ is the number of tokens in the state we
resume from and $n$ is the number of tokens to parse. Parsing an increment of
constant size has an amortized complexity of $O(1)$.

The parsing library presented in this paper is 
used in the Yi editor to help matching parenthesis and layout the Haskell
functions, and environment delimiters as well as parenthetical
symbols were matched in the \LaTeX{} source.

This paper and accompanying source code have been edited in this environment.


\section{Conclusion}
\label{sec:conclusion}

\textmeta{Review}

We have shown that the combination of three techniques
achieve the goal of incremental parsing.

\begin{enumerate}

\item In a lazy setting, the combination of online production of results and
saving intermediate results provide incrementality;

\item Online parsers can be extended with an error correction scheme for
modularity.

\item Provided that they are carefully constructed to preserve laziness, tree
structures can always replace lists in functional programs. Doing so can improve
the complexity class of algorithms.

\end{enumerate}

While these techniques work together here, we believe that they are valuable
independently of each other. In particular, our error correction scheme can be
replaced by an other one without invalidating the approach. 

Also, while functional data structures are often presented in a way that
ignores their lazy constructions (and thus are not always as good as plain
lists), we have shown that this need not be the case. The simple structure
presented here has three applications in our system only, and is virtually always
an improvement over plain lists.




\acks

We thank Koen Claessen for persuading us to write this paper, and for his
unfading support throughout the writing process. This paper was greatly improved
by his comments on early and late drafts. Krasimir Angelov helped sorting out
the notions of incremental parsing. Patrick Jansson, Wouter Swierstra, Gustav Munkby, Marcin Zalewski
\textmeta{!!!Your name here!!!}
gave helpful comments on drafts.

\bibliographystyle{mybst}
\bibliography{../Zotero.bib}
\section*{Appendix: The complete code}
The complete code of the library described in this paper can be found here: \url{http://github.com/jyp/topics/tree/master/FunctionalIncrementalParsing/Code.lhs}

% %include Code.lhs

\end{document}

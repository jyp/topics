% -*- latex -*-
\documentclass[utf8x,compress]{beamer}
%include lhs2TeX.fmt
%format :*: = " \applbind"
%format :|: = " \disjunct"
%format :# = " \prog"
%format +> = " \secondPush"
\usepackage{graphicx}
\usepackage[utf8x]{inputenc}
\usepackage{pgf}
\usepackage{pgfpages}
% \setbeameroption{notes on second screen}
\usepackage{tikz}
\usetikzlibrary{trees,positioning,arrows}

\usetheme{Malmoe}

\pgfdeclareimage[height=1cm]{yi-logo}{../talk/yi+lambda-fat}
\pgfdeclareimage[height=1cm]{university-logo}{../talk/ChalmGUmarke}
% \logo{\pgfuseimage{university-logo}}

\newtheorem{idea}{Idea}
 
\newcommand{\applbind}{\mathbin{:\!\!*\!\!:}}
\newcommand{\disjunct}{\mathbin{:\!\!||\!\!:}}
\newcommand{\secondPush}{\mathbin{+\!\!>}}
\newcommand{\prog}{\ensuremath{\mathbin{:\!\!\#}}}


\title{Lazy Functional Incremental Parsing}
\author{Jean-Philippe Bernardy}
\institute {Chalmers University of Technology
           % and University of Gothenburg
           }
\date {
    \today
      }

\begin{document}

\frame{\titlepage
  \begin{center} \pgfuseimage{university-logo} \end{center}
}

\frame{
    \frametitle{Outline}
    \tableofcontents
}

\section{From motivation to specification}

\frame{
  \frametitle{Motivation: Syntax-aware editor}

  \begin{idea}[Syntax-aware editor]
     All syntax-dependent features should be based on the \textbf{same} AST
  \end{idea}
  \include{overview}

}



\frame{
  \frametitle{A special kind of parser}

  Requirements on the parser:
  \begin{itemize}
      \item \emph{Incremental}: In sync with input (i.e. fast) 
      \note{fast => independent from length of input}
      \item \emph{Error-correcting}: Must cope with all inputs
      \note{The user can edit in partially correct states!}
  \end{itemize} 
  \pause
  ... so I cannot re-use the parser of my favourite compiler.
}



\begin{frame}
    \frametitle{Approach to incrementality}
    \begin{itemize}
        \item Save intermediate parser states after each symbol
\note{
    Each parser state record the state of the parsing process after
    having fully processed the input up to the corresponding point.

Moving down the file, parse some more symbol using the state at the current
point. Moving up: just go up the list. Edit: discard the right part of the list.

    Cacheing these provide incrementality of parsing, if you are only
    interested at the parser state at the current point of input.
}

        \item<2-> Use lazy evalutation to expose each state as a tree
\note{
    
    One cannot do much with the parser state. We want an AST!
    The state normally contains the AST "so far" though. (The dark part).
    Idea: lazily complete the AST with a "thunk" dependent on the rest of the input.

    (In other words, Each parser states contains a partially computed AST, with
    "holes" that correspond to the parts of the unprocessed input.)

    From here on the eagerly computed part of the AST is the ``dark part'', the 
    lazily computed on is called the ``light part''.
}
    \end{itemize}


\begin{center}
\begin{tikzpicture}[scale=0.75,transform shape,>=latex,join=bevel]
  \pgfsetlinewidth{1bp}
%include states.tex
\end{tikzpicture}
\begin{overlayarea}{\textwidth}{3cm}
\includegraphics<2->{progress}
\end{overlayarea}
\end{center}


\end{frame}

\frame{
\frametitle{Zoom on the current AST}
\begin{center}
    \includegraphics[height=4cm]{ast}
\end{center}

\begin{itemize}
    \item Incremental 
\note{
    The situation:
      * Accessing the dark part is for free (cached) thus "truly" incremental; 
      * Accessing the light part is costly, more so to the extreme right.
      * Displaying may force a little more
        parsing, up to the end of the window (the blue part).
}
    \item Functional 
\note{
    The beauty of this system is that there is never any update of the AST, only
    the list of cached states is updated. The state is simple.
}
    % \item Lazy \note{We take advantage of laziness! -- does not require explanation}
\end{itemize}

}

\frame{
  \frametitle{Technical Goals}
  \begin{itemize}
  \item Two types of parsing: eager and lazy.
  \begin{itemize}
    \item |runEager :: Process s a -> [s] -> Process s a|
    \note{Because the parser states must fully process the input
          so far, we have to provide an eager parsing procedure.}
    \item |runLazy  :: Process s a -> [s] -> a|
  \end{itemize}

  \item Error correction

  \item Parser-combinator library
  \begin{itemize}
    \item |mkProcess :: Parser s a -> Process s a|
  \end{itemize}
  \end{itemize}
}

\section{Some essential components}


\begin{frame}[fragile]
  \frametitle{Combinators}
 
\begin{itemize}
 \item Applicative interface
 \item Dependence on input 
 \item Alternative interface (beware of errors!)
\end{itemize}

\begin{verbatim}
data Parser s a where
  Pure  :: a                               -> Parser s a
  (:*:) :: Parser s (b -> a) -> Parser s b -> Parser s a
  Symb  :: (Maybe s -> Parser s a)         -> Parser s a
  Disj  :: Parser s a -> Parser s a        -> Parser s a
  Yuck  :: Parser s a                      -> Parser s a
\end{verbatim}
% Bin   (Bin   (Leaf   1)   (Leaf   2))   (Symb ...            )
% Bin $ (Bin $ (Leaf $ 1) $ (Leaf $ 2)) $ (Symb ...            )


\end{frame}

\subsection{Incrementality}

\begin{frame}[fragile]
  \frametitle{Support of eager + lazy}

    Starting point: Polish Parsers (Hughes \& Swierstra 2001).
\begin{idea}
    Linearize applications by transforming to polish form. |(:*:)|
\end{idea}

\note{just a simple example to remind what polish notation looks like}
| (7 - (2 * 3)) + (1 - ...) |\\
| + - 7 * 2 3 - 1 ... |


%     Bin $ (    Bin $ (  Leaf $ 1) $ (  Leaf $ 2)) $ (Symb   )
% $ $ Bin    $ $ Bin    $ Leaf   1  $  $ Leaf   2     (Susp   )
% \end{verbatim}
\pause
\note{It's the same for Parser, but there is just one operator (application)}
\begin{verbatim}
data Polish r where
  Push :: a -> Polish r               -> Polish (a :< r)
  App  :: Polish ((b -> a) :< b :< r) -> Polish (a :< r)
  Done ::                                Polish Nil
\end{verbatim}

\note{Polish expressions can be understood as stack transformers}
\note{|:<| represents a stack of things}

\begin{verbatim}
toPolish :: Parser s a -> Polish (a :< Nil)
toPolish expr = toP expr Done
  where toP :: Parser s a -> (Polish r -> Polish (a :< r))
        toP (Pure x)   = Push x
        toP (f :*: x)  = App . toP f . toP x
\end{verbatim}

\note{Making the structure of applications explicit allows to 
\begin{itemize}
    \item add more features (dependence of inputs)
    \item control precisely the evaluation mechanism
\end{itemize}
}  

\end{frame}

\frame{
  \frametitle{Lazy evaluation}
\begin{verbatim}
evalLazy :: Polish r -> r
evalLazy (Push a r)  = a :< evalLazy r
evalLazy (App s)     = apply (evalLazy s)
    where  apply ~(f :< ~(a:<r))  = f a :< r
evalLazy (Done)      = Nil
\end{verbatim}  
}

\frame{
    \frametitle{Eager evaluation (sketch)}
    Precompute (in prefixes of) polish expression.

| + - 7 * 2 3 - 1 ... |

% \begin{verbatim}
% $ $ Bin    $ $ Bin    $ Leaf   1   $ Leaf   2     (Susp )
% \end{verbatim}
\begin{verbatim}
evalEager :: Polish r -> Polish r
evalEager (Push x r) = Push x (evalEager r)
evalEager (App f) = case evalEager f of
     (Push g (Push b r)) -> Push (g b) r
     r -> App r
evalEager p = p
\end{verbatim}
}

\frame{
  \frametitle{Polish Zipper}
| + - 7 * 2 3 || - 1 ... |
% $ $ Bin    $ $ Bin    $ Leaf  |  1    $ Leaf   2    (Susp )
\pause
\begin{verbatim}

data Zip s out where
  Zip :: RPolish stack out -> Polish stack -> Zip out

data RPolish inp out where
  RPush :: a -> RPolish (a :< r) out ->
               RPolish r out
  RApp  :: RPolish (b :< r) out ->
               RPolish ((a -> b) :< a :< r) out 
  RStop :: RPolish r r
\end{verbatim}

\begin{verbatim}
right :: Zip s out -> Zip s out
right (Zip l (Push a r))  = Zip (RPush a l) r
right (Zip l (App r))     = Zip (RApp l) r   
right (Zip l s)           = Zip l s
\end{verbatim}

}

\frame{
  \frametitle{Eager evaluation revisited}
Keep the reverse automaton normalized: after moving to the right, iterate simplify.
% \begin{verbatim}
% + - 7 * 2 3 | - 1 ...
% + - 7 6     | - 1 ...
% + 1         | - 1 ...
% \end{verbatim}

|+ - 7 * 2 3 || - 1 ... | \\
|+ - 7 6     || - 1 ... | \\
|+ 1         || - 1 ... | \\

\begin{verbatim}
simplify :: RPolish s output -> RPolish s output
simplify (RPush a (RPush f (RApp r))) = 
    simplify (RPush (f a) r)
simplify x = x
\end{verbatim}



% $ $ Bin    $ $ Bin    $ Leaf   1 | $ Leaf   2     (Susp  )
% $ $ Bin    $ $ Bin    (Leaf 1)   | $ Leaf   2     (Susp  )
% $ $ Bin    $ (Bin (Leaf 1))      | $ Leaf   2     (Susp  )

\note{Dark part: an AST with holes; light parts: plugs for these holes.}
}

\frame{
  \frametitle{Summary}
  \begin{itemize}
      \item State = Polish Zipper structure
      \item runEager = resolve some suspensions; traverse right and simplify.
      \item runLazy = resolve all suspensions; traverse left and lazy evaluate. (lazily)
      \item Left Part ↝ Dark green
      \item Right Part ↝ Light green
  \end{itemize}
}

\subsection{Error-correction}

\frame {
    \frametitle{Error reporting}
    Where should errors be put?
    \begin{itemize}
        \item In the syntax tree (placeholder nodes)
        \item As a separate list of errors
    \end{itemize}
}

\section{Conclusion}

\frame{
\frametitle{Summary}

Ingredients:
\begin{itemize}
\item Lazy evaluation
\item Zipper
\item Sexy types
\item ...
\end{itemize}

\pause
Result: Parser-combinator library
\begin{itemize}
\item
  Error correction
\item
  Incremental

\begin{itemize}
   \item eager + lazy
   \item no AST update
\end{itemize}
\end{itemize}

\pause
Application: Syntax-aware editor
}


\frame{
\frametitle{Perspective}
\begin{tabular}{lcc}
  Method & Forward & \uncover<2->{Bottom-up} \\
  \hline 
  Update & List of states & \uncover<2->{The parser state}  \\
  AST Consumer & Must be lazy & \uncover<2->{No constraint} \\
  Parser & limited lookahead & \uncover<2->{No constraint}  \\
  Startup cost & none & \uncover<2->{one full parse} \\
\end{tabular}
}




\end{document}


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
     All syntax-dependent applications should use the same interface: the AST
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
  \end{itemize} 
  \pause
  ... so I cannot re-use the parser of my favourite compiler.
}



\begin{frame}
    \frametitle{Approach to incrementality}
    \begin{itemize}
        \item Save intermediate parser states
        \item<2-> Use lazy evalutation to expose each state as a tree
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
\note{
    From here on the eagerly computed part of the AST is the ``dark part'', the 
    lazily computed on is called the ``light part''.
}

\end{frame}



\frame{
  \frametitle{Technical Goals}
  \begin{itemize}
  \item Two types of parsing: eager and lazy.
  \begin{itemize}
    \item |runEager :: Process s a -> [s] -> Process s a|
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

\begin{verbatim}
data Parser s a where
  Pure  :: a                               -> Parser s a
  (:*:) :: Parser s (b -> a) -> Parser s b -> Parser s a
  Symb  :: (Maybe s -> Parser s a)         -> Parser s a
  Disj  :: Parser s a -> Parser s a        -> Parser s a
  Yuck  :: Parser s a                      -> Parser s a


\end{verbatim}
\end{frame}

\subsection{Incrementality}

\begin{frame}[fragile]
  \frametitle{Support of eager + lazy}

    Starting point: Polish Parsers (Hughes \& Swierstra 2001).
\begin{idea}
    Linearize |(:*:)|
\end{idea}

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
    Precompute prefixes of polish expression.
\begin{verbatim}
evalEager :: Polish s a -> Polish s a
evalEager (Push x r) = Push x (evalEager r)
evalEager (App f) = case evalEager f of
     (Push g (Push b r)) -> Push (g b) r
     r -> App r
evalEager p = p
\end{verbatim}
}

\frame{
  \frametitle{Polish Zipper}
\begin{verbatim}
data Zip s out where
  Zip :: RPolish stack out -> Polish s stack -> Zip s out

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
Keep the reverse automaton normalized: after moving to the right, simplify.
\begin{verbatim}
simplify :: RPolish s output -> RPolish s output
simplify (RPush a (RPush f (RApp r))) = 
    simplify (RPush (f a) r)
simplify x = x
\end{verbatim}
\note{Dark part: an ast with holes; light parts: plugs for these holes.}
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


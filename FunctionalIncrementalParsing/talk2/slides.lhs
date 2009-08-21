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
    \begin{itemize}
        \item From motivation to specification.
        \item Some essential components of incremental parsing.
    \end{itemize}
}

\frame{
  \frametitle{Motivation: Interactive Parsing}

  \begin{idea}
     All syntax-dependent applications should use the same interface: the AST
  \end{idea}
  \include{overview}

}



\frame{
  \frametitle{A special kind of parser}

  \begin{itemize}
      \item \emph{Incremental}: In sync with input (ie. fast)
      \item \emph{Error-correcting}: Must cope with all inputs
  \end{itemize}
}



\begin{frame}
    \frametitle{Approach}
    \begin{itemize}
        \item Save intermediate parser states.
        \item Use lazy evalutation to expose each state as a tree.
    \end{itemize}

\begin{center}
\begin{tikzpicture}[scale=0.75,transform shape,>=latex,join=bevel]
  \pgfsetlinewidth{1bp}
%include states.tex
\end{tikzpicture}

\includegraphics{progress}
\end{center}

\end{frame}



\frame{
  \frametitle{Technical Goals}
  \begin{itemize}
  \item Parser-combinator library
  \item Two types of parsing: eager and lazy.
  \begin{itemize}
    \item |runEager :: Process s a -> [s] -> Process s a|
    \item |runLazy  :: Process s a -> [s] -> a|
    \item (|mkProcess :: Parser s a -> Process s a|)
  \end{itemize}

  \item Error correction
  \end{itemize}
}



\begin{frame}[fragile]
  \frametitle{Interface}

\begin{verbatim}
data Parser s a where
  Pure  :: a                               -> Parser s a
  (:*:) :: Parser s (b -> a) -> Parser s b -> Parser s a
  Symb  :: (Maybe s -> Parser s a)         -> Parser s a
  Disj  :: Parser s a -> Parser s a        -> Parser s a
  Yuck  :: Parser s a                      -> Parser s a


\end{verbatim}
\end{frame}

\begin{frame}[fragile]
  \frametitle{Supporting this interface}

    Starting point: Polish Parsers (Hughes \& Swierstra 2001).
    Idea: linearizing |(:*:)|.

\begin{verbatim}
data Polish r where
  Push :: a -> Polish r               -> Polish (a :< r)
  App  :: Polish ((b -> a) :< b :< r) -> Polish (a :< r)
  Done ::                                Polish Nil
\end{verbatim}

\begin{verbatim}
toPolish :: Parser s a -> Polish (a :< Nil)
toPolish expr = toP expr Done
  where toP :: Parser s a -> (Polish r -> Polish (a :< r))
        toP (f :*: x)  = App . toP f . toP x
        toP (Pure x)   = Push x
\end{verbatim}
  
\end{frame}

\frame{
  \frametitle{Online}
\begin{verbatim}
evalLazy :: Polish r -> r
evalLazy (Push a r)  = a :< evalLazy r
evalLazy (App s)     = apply (evalLazy s)
    where  apply ~(f :< ~(a:<r))  = f a :< r
evalLazy (Done)      = Nil
\end{verbatim}
  
}

\frame{
    \frametitle{Offline (idea)}
    Precompute prefixes of polish expression.
\begin{verbatim}
evalEager :: Polish s a -> Polish s a
evalEager (Push x r) = Push x (evalEager r)
evalEager (App f) = case evalEager f of
                  (Push g (Push b r)) -> Push (g b) r
                  r -> App r
\end{verbatim}
}

\frame{
  \frametitle{Offline (zipper)}
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
  \frametitle{Offline (computation)}
\begin{verbatim}
evalRP :: RPolish inp out -> inp -> out
evalRP RStop acc          = acc 
evalRP (RPush v r) acc    = evalRP r (v :< acc)
evalRP (RApp r) ~(f :< ~(a :< acc)) 
                          = evalRP r (f a :< acc)
\end{verbatim}
}

\frame {
    \frametitle{Error reporting}
    Where should errors be put?
    \begin{itemize}
        \item In the syntax tree (placeholder nodes)
        \item As a separate list of errors
    \end{itemize}
}



\frame{
\frametitle{Results}

\begin{itemize}

\item
  Functional approach to incremental parsing (AST never updated, only state-list is updated)

\item
  No startup cost

\item
  Usable

\item
   Available as a parser-combinator library
\begin{itemize}
\item
  Eager+Lazy

\item
  Error correction
\end{itemize}

}

\frame{
\frametitle{Issues}
\begin{itemize}
\item Lots of constraints of the user:
\item AST must be consumed lazily
\item Grammar must not use too much lookahead
\end{itemize}
}

\frame{
\frametitle{Future work}
Bottom up parsing?
}


\end{document}


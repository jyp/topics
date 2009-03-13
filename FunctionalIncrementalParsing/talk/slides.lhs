% -*- latex -*-
\documentclass[utf8x,compress]{beamer}
%include lhs2TeX.fmt
%format :*: = " \applbind"
%format :|: = " \disjunct"
%format :# = " \prog"
%format +> = " \secondPush"
\usepackage{graphicx}
\usepackage[utf8x]{inputenc}
\usetheme{Malmoe}

\pgfdeclareimage[height=1cm]{yi-logo}{yi+lambda-fat}
\pgfdeclareimage[height=1cm]{university-logo}{ChalmGUmarke}
% \logo{\pgfuseimage{university-logo}}
 
\newcommand{\applbind}{\mathbin{:\!\!*\!\!:}}
\newcommand{\disjunct}{\mathbin{:\!\!||\!\!:}}
\newcommand{\secondPush}{\mathbin{+\!\!>}}
\newcommand{\prog}{\ensuremath{\mathbin{:\!\!\#}}}


\title{Lazy and Incremental Parsing}
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
  \frametitle{Demo}
}

\frame{
  \frametitle{Motivation}
   Using ad-hoc techniques for all the syntax-related operations is not satisfying...
   
   I want a real parser!
}

\frame{
  \frametitle{Goals}
  I want a parsing library...
  \begin{itemize}
  \item programmable through a combinator interface;
  \item able to cope with all inputs provided by the user (error correcting);
  \item efficient enough for interactive usage: parsing must be done incrementally.
  \end{itemize}
}

\frame{
  \frametitle{Approach}
  \includegraphics[width=5cm]{begin}
\pause
  \includegraphics[width=5cm]{mid}
}


\begin{frame}[fragile]
  \frametitle{Interface}

\begin{itemize}
 
 \item |mkProcess :: Parser s a -> Process s a|
 \item |feed :: [s] -> Process s a -> Process s a|
 \item |feedEof :: Process s a -> Process s a|
 \item |precompute :: Process s a -> Process s a|
 \item |finish :: Process s a -> a|
\end{itemize}

\pause
\begin{verbatim}
data Parser s a where
  Pure   :: a                               -> Parser s a
  (:*:)  :: Parser s (b -> a) -> Parser s b -> Parser s a
  Symb   :: Parser s a -> (s -> Parser s a) -> Parser s a
  Disj   :: Parser s a -> Parser s a        -> Parser s a
  Yuck   :: Parser s a                      -> Parser s a
\end{verbatim}

\end{frame}

\begin{frame}[fragile]
  \frametitle{Supporting this interface}

\begin{itemize}
 \item Input is linear... linearize everything.
 \item Linearizing |(:*:)|
 \item Linearizing |Disj| 
 \item Compute results in online way.
 \item Compute results in offline way.
\end{itemize}

\end{frame}

\frame{
  \frametitle{Linearizing |(:*:)|}

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
  
}

\frame{
  \frametitle{Online}
\begin{verbatim}
evalR :: Polish r -> r
evalR (Push a r)  = a :< evalR r
evalR (App s)     = apply (evalR s)
    where  apply ~(f :< ~(a:<r))  = f a :< r
evalR (Done)      = Nil
\end{verbatim}
  
}

\frame{
  \frametitle{Offline}
\begin{verbatim}
data Zip s out where
  Zip :: RPolish stack out -> Polish s stack -> Zip s out

data RPolish inp out where
  RPush  :: a -> RPolish (a :< r) out ->
               RPolish r out
  RApp   :: RPolish (b :< r) out ->
               RPolish ((a -> b) :< a :< r) out 
  RStop  ::    RPolish r r
\end{verbatim}

\begin{verbatim}
evalRP :: RPolish inp out -> inp -> out
evalRP RStop acc          = acc 
evalRP (RPush v r) acc    = evalRP r (v :< acc)
evalRP (RApp r) ~(f :< ~(a :< acc)) 
                          = evalRP r (f a :< acc)
\end{verbatim}
}

\frame{
\frametitle{Contributions}

Our contributions can be summarized as follows.

\begin{itemize}
\item
  Purely functional approach to incremental parsing
\item
  Essential use of lazy evaluation. 

\item
  Error correction.

\item
  Parser-combinator library;

\item
  Used in a real editor.

\end{itemize}
}



\end{document}


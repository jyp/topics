% -*- latex -*-
\documentclass[preprint,natbib]{../../tex/sigplanconf}
%include lhs2TeX.fmt
\usepackage{ifpdf}

\ifpdf
  % Use letter format.
  \pdfpagewidth=8.5in
  \pdfpageheight=11in

  \pdfinfo{
    /Title (Testing Polymorphic Functions)
    /Author (Jean-Philippe Bernardy, Patrik Jansson and Koen Claessen)
  }
\fi

%\usepackage{amsmath}
%\usepackage{amsfonts}
\usepackage{url}   % For \url.
%\usepackage{nopageno} % No page numbers.
\usepackage{natbib}

%\usepackage{ucs}
\usepackage[utf8x]{inputenc}
%\usepackage{autofe}

\newcommand{\todo}[1]{{\it \textbf{TODO:} #1}}

% An itemize environment with less spacing. Stolen from the
% UK TUG TeX FAQ.
\newenvironment{itemize*}%
  {\begin{itemize}%
    \setlength{\itemsep}{0pt}%
    \setlength{\parskip}{0pt}}%
  {\end{itemize}}

\begin{document}

\conferenceinfo{POPL'10}%
{January 21--23, 2010, Madrid, Spain.}
\CopyrightYear{2010}
%\copyrightdata{}

\title{Testing Polymorphic Functions\thanks{This work is partially
    funded by the Swedish Research Council.}}

\authorinfo{Jean-Philippe Bernardy \and Patrik Jansson
  \and Koen Claessen}
  {Chalmers University of Technology}
  {\{bernardy,patrikj,koen\}@@chalmers.se}

\titlebanner{Draft}                     % These are ignored unless
\preprintfooter{Submitted to POPL'10}   % 'preprint' option specified.

\maketitle

\begin{abstract}
  Many useful functions are parametrically polymorphic. 
  Testing can only be applied to monomorphic instances of polymorphic functions.
  If we verify correctness of one instance, what do we know of all the other instances?
  We present a schema for constructing a monomorphic type such that correctness of that single instance implies correctness for all other instances.
\end{abstract}

% See http://www.acm.org/class/ for details about
% categories etc.

\category{F.3.1}{Logics and Meanings of Programs}{Specifying and
  Verifying and Reasoning about Programs} % [Logics of programs]
\category{D.3.2}{Programming Languages}{Language Classifications}[Applicative (functional) languages]

% Something about testing should be added

% Some other remotely related categories:

% \category{F.3.3}{Logics and Meanings of Programs}{Studies
%   of Program Constructs}[Program and recursion schemes,
%   Type structure]

% \category{F.3.2}{Logics and Meanings of Programs}{Semantics
%   of Programming Languages}[Denotational Semantics]

% \category{D.3.1}{Programming Languages}{Formal Definitions
%   and Theory}[Semantics]

% \category{F.4.1}{Mathematical Logic and Formal
%   Languages}{Mathematical Logic}[Model theory, Proof
%   theory, Lambda calculus and related systems]

\terms Languages, verification, testing

\keywords 

\section{Intro}
\section{Example}
\section{Theory}
\section{Testing}
\section{Related work}


QuickCheck \cite{claessen-hughes-quickcheck}

Something from this group:
\begin{itemize}
\item A theory of type polymorphism in programming \cite{milner78}
\item Types, abstraction, and parametric polymorphism \cite{reynolds83}
\item Theorems for free! \cite{wadler89}
\end{itemize}

Testing properties of generic functions \cite{janssonjeuring2007:Testing}

Fast and loose reasoning? \cite{danielssonetal06:fastandloose}
  (at least we could use some terminology and perhaps notation from that paper)

Possibly something about this:
Free Theorems in the Presence of seq \cite{johann-voigtlander-seq}


\section{Conclusions}
\paragraph{Acknowledgements}

\bibliography{../../bibtex/genprog,../../bibtex/misc}
\bibliographystyle{abbrvnat}

\end{document}

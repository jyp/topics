% -*- latex -*-
\ignore{

\begin{code}
{-# LANGUAGE TypeOperators, GADTs #-}
module Applicative where
import SExpr
import Stack
\end{code}

}

%format UPolish = Polish
%format UPush = Push
%format UApp = App
%format UDone = Done
\section{Producing results} 
\label{sec:applicative}

\citet{hughes_polish_2003} show that the sequencing operator must be
applicative (\citet{mcbride_applicative_2007}) to allow for online production of
results. This result is the cornerstone of our approach to incremental parsing,
so we review it in this section, justifying the use of the combinators |Pure|
and |(:*:)|, which form the applicative sub-language.

We also introduce the \emph{polish representation} for applicative
expressions: it is the essence of our parsing semantics. This
section culminates in the definition of the pipeline from applicative language
to results by going through polish expressions. Our final parser (section \ref{sec:choice}) is an
extension of this machinery with the all the features mentioned in the introduction.

% \subsection{The applicative sub-language}

A requirement for online production of the result is that nodes are
available before their children are computed. In terms of datatypes, this means that
constructors must be available before their arguments are computed. This can only be done if the
parser can observe (pattern match on) the structure of the result. Hence, we make function
applications explicit in the expression describing the results.

For example, the Haskell expression |S [Atom 'a']|, which stands for |S ((:)
(Atom 'a') [])| if we remove syntactic sugar, can be represented in applicative
form by

\begin{spec}
S @ ((:) @ (Atom @ 'a') @ [])
\end{spec}

The following data type captures a pure applicative language embedding
 Haskell values. It is indexed by the type of values it represents.

\begin{code}
data Applic a where
    (:*:)  :: Applic (b -> a) -> Applic b    -> Applic a
    Pure   :: a                              -> Applic a
infixl 4 :*:
\end{code}

The application annotations can then be written using Haskell syntax as follows:

\begin{spec}
Pure S :*: (Pure (:)  :*: (Pure Atom :*: Pure 'a') 
                      :*: Pure [])
\end{spec}

We can also write a function for evaluation:

\begin{code}
evalA :: Applic a -> a
evalA (f :*: x)  = (evalA f) (evalA x)
evalA (Pure a)   = a
\end{code}

If the arguments to the |Pure| constructor are constructors, then we know that
demanding a given part of the result forces only the corresponding part of
the applicative expression. 

% In that case, the |Applic| type effectively allows us to define partial computations and reason about them.

Because our parsers process the input in a linear fashion, they require a
linear structure for the output as well. (This is revisited in section~\ref{sec:parsing}). As
\citet{hughes_polish_2003}, we convert the applicative expressions to their polish
representation to obtain such a linear structure.

The key idea of the polish representation is to put the application in a
prefix position rather than an infix one. Our example expression (in applicative form 
|S @ ((:) @ (Atom @ 'a') @ [])|)
becomes
|@ S (@ (@ (:) (@ Atom 'a') []))|

Since |@| is always followed by exactly two arguments, grouping information can
be inferred from the applications, and the parentheses can be dropped. The final
polish expression is therefore

\begin{spec}
@ S @ @ (:) @ Atom 'a' []
\end{spec}

The Haskell datatype can also be linearized in the same way. Using |App| for
|@|, |Push| to wrap values and |Done| to finish the expression, we obtain the
following representation.

\begin{spec}
 App $ Push S $ App $ App $ Push (:) $ 
   App $ Push Atom $ Push 'a' $ Push [] $ Done
\end{spec}

\begin{code}
data UPolish where
    UPush  :: a -> UPolish      ->  UPolish
    UApp   :: UPolish           ->  UPolish
    UDone  ::                       UPolish
\end{code}


Unfortunately, the above datatype does not allow to evaluate expressions in a
typeful manner. The key insight is that polish expressions are in fact more
general than applicative expressions: they produce a stack of values instead of
a single one.

As hinted by the constructor names we chose, we can reinterpret polish
expressions as follows. |Push| produces a stack with one more value than its
argument, |App| transforms the stack produced by its argument by applying the
function on the top to the argument on the second position, and |Done| produces
the empty stack.

The expression |Push (:) $ App $ Push Atom $ Push 'a' $ Push [] $ Done| is an
example producing a non-trivial stack. It produces the stack |(:) (Atom 'a')
[]|, which can be expressed purely in Haskell as |(:) :< Atom 'a' :< [] :< Nil|,
using the following representation for heterogeneous stacks.

%include Stack.lhs

We are now able to properly type polish expressions, by indexing the datatype
with the type of the stack produced.

\begin{code}
data Polish r where
    Push  :: a -> Polish r                  ->  Polish (a :< r)
    App   :: Polish ((b -> a) :< b :< r)    ->  Polish (a :< r)
    Done  ::                                    Polish Nil
\end{code}

We can also write a translation from the pure applicative language to
polish expressions.

\begin{code}
toPolish :: Applic a -> Polish (a :< Nil)
toPolish expr = toP expr Done
  where  toP :: Applic a -> (Polish r -> Polish (a :< r))
         toP (f :*: x)  = App . toP f . toP x
         toP (Pure x)   = Push x
\end{code}

And the value of an expression can be evaluated as follows:

\begin{code}
evalR :: Polish r -> r
evalR (Push a r)  = a :< evalR r
evalR (App s)     = apply (evalR s)
    where  apply ~(f :< ~(a:<r))  = f a :< r
evalR (Done)      = Nil
\end{code}

% evalR :: Polish (a :< r) -> (a, Polish r)
% evalR (Push a r) = (a,r)
% evalR (App s) =  let  (f, s') = evalR s
%                       (x, s'') = evalR s'
%                  in (f x, s'')

We have the equality |evalR (toPolish x) == evalA x :< Nil|.

% Patrik: and: evalR (toP x r) == evalA :< evalR r

Additionally, we note that this evaluation procedure still possesses the ``online''
property: prefixes of the polish expression are demanded only if the corresponding
parts of the result are demanded. This preserves the incremental properties of
lazy evaluation that we required in the introduction. Furthermore, the equality
above holds even when |undefined| appears as argument to the |Pure| constructor.
In fact, the conversion from applicative to polish expressions can be understood as 
a reification of the working stack of the |evalA| function with call-by-name
semantics.

% \textmeta{Now one has to be careful not to break this when adding features.}

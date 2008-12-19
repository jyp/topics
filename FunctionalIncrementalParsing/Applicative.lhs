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


Our goal is to provide a combinator library with an interface similar to that
presented by \citet{swierstra_combinator_2000}, with sequencing, disjunction,
production of results and reading of symbols. 
% Such an interface can be captured
% in a GADT as follows. (Throughout this paper we will make extensive use of GADT
% for modeling purposes.)
% 
% \begin{code}
% data Parser s a where
%     Pure   :: a                                  ->  Parser s a
%     (:*:)  :: Parser s (b -> a) -> Parser s b    ->  Parser s a
%     Symb   :: Parser s a -> (s -> Parser s a)    ->  Parser s a
%     Disj   :: Parser s a -> Parser s a           ->  Parser s a
%     Fail   ::                                        Parser s a
% \end{code}
% 
\textmeta{I don't like to give the parser type here already. There is a perfectly good explanation to comeup with the applicative stuff; pulling the full thing out of my hat renders the following argument futile.}

However, in this section we step back and concentrate solely on constructing
parsing results, ignoring the dependence on input. 
% This leaves us with the constructors |Pure| and |(:*:)|.


The cornerstone of our
approach to incremental parsing is that the parse tree is produced
\emph{online}. We can ensure that this is the case by forcing the structure of
the result to be expressed in applicative (\citet{mcbride_applicative_2007})
form.

The idea is to make function applications explicit. 

For example, the Haskell expression |S [Atom 'a']|, which stands for |S ((:)
(Atom 'a') [])| if we remove syntactic sugar, can be represented in applicative
form by

\begin{spec}
S @ ((:) @ (Atom @ 'a') @ [])
\end{spec}


The following data type captures the pure applicative language with embedding
of Haskell values. It is indexed by the type of values it represents.

\begin{code}
data Applic a where
    (:*:) :: Applic (b -> a) -> Applic b    -> Applic a
    Pure :: a                               -> Applic a
infixl :*:
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

If the arguments to the |Pure| constructor are constructors, then we know that demanding a given part of the result will force
only the corresponding part of the applicative expression. In that case, the
|Applic| type effectively allows us to define partial computations and reason
about them.

Because they process the input in a linear fashion, our parsers require a
linear structure (it will become apparent in section~\ref{sec:parsing}). As
\citet{hughes_polish_2003}, we convert the applicative expressions to polish
representation to obtain such a linear structure.

The key idea of the polish representation is to put the application in an
prefix position rather than an infix one. Our example expression (in applicative form 
|S @ ((:) @ (Atom @ 'a') @ [])|)
becomes
|@ S (@ (@ (:) (@ Atom 'a') []))|

Since |@| is always followed by exactly two arguments, grouping information can
be inferred from the applications, and the parenthesises can be dropped. The final
polish expression is therefore

\begin{spec}
@ S @ @ (:) @ Atom 'a' []
\end{spec}

The Haskell datatype can also be linearized in the same way, yielding the following
representation for the above expression.

\begin{code}
x = App $ Push S $ App $ App $ Push (:) $ 
   App $ Push Atom $ Push 'a' $ Push [] $ Done
\end{code}

\begin{code}
data UPolish where
    UPush  :: a -> UPolish      ->  UPolish
    UApp   :: UPolish           ->  UPolish
    UDone  ::                       UPolish
\end{code}


Unfortunately, the above datatype does not allow to evaluate expressions in a
typeful manner. The key insight is to that polish expressions are in fact more
general than applicative expressions: they produce a stack of values instead of
just one.

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

We can now write a translation from the pure applicative language to
polish expressions.

\begin{code}
toPolish :: Applic a -> Polish (a :< Nil)
toPolish expr = toP expr Done
  where toP :: Applic a -> (Polish r -> Polish (a :< r))
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

We have the equality |top (evalR (toPolish x)) == evalA x|.

Additionally, we note that this evaluation procedure still possesses the ``online''
property: parts of the polish expression are demanded only if the corresponding
parts of the input is demanded. This preserves the incremental properties of
lazy evaluation that we required in the introduction. Furthermore, the equality
above holds even when |undefined| appears as argument to the |Pure| constructor.

In fact, the conversion from applicative to polish expressions can be understood as 
a reification of the working stack of the |evalA| function with call-by-name
semantics.

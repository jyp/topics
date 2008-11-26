% Functional Incremental Parsing 
% Jean-Philippe Bernardy

# Abstract

In the context of an interactive application where the user observes only a
small window of the output (that is, one that corresponds to a small window of
the input), we show that combining lazy evaluation and caching of intermediate (partial)
results provides incremental parsing. We also introduce a general purpose,
simple data structure, to get rid of the linear complexity caused by lazy lists
traversals while retaining its lazy properties. Finally, we complete our 
treatment of incremental parsing in an interactive system by showing how
our parsing machinery can be improved to support error-correction.

# Introduction

In an interactive system, a lazy evaluation strategy provides a special form
of incremental computation: the amount of output that is demanded drives the
computation to be performed. In other words, the system responds to incremental
movement of the portion of the output being viewed by the user (window) by
incremental computation of the intermediate structures.

This suggests that we can take advantage of lazy evaluation to implement
incremental parsing for an interactive application. Indeed, if we suppose that
the user makes changes in the input that "corresponds to" the window being
viewed, it suffices to cache partially computed results for each point in the
input, to obtain a system that responds to changes in the input independently
of the total size of that input.

In the Yi editor, we used this technique to provide features such as syntax
highlighting and indentation hints for the Haskell language. The abstract
syntax tree (AST) being available at all times is very convenient to implement
all syntax-dependent functions in a consistent way.

In this paper, we will use a simpler problem for the purpose of illustration:
parenthesis matching for a lisp-like language. Given an input
such as `1 + (5 * (3 + 4)) * 2`, the program will display `1 + {5 * [3 + 4]} *
2`. The idea is that matching pairs are displayed using different parenthetical
symbols for each level, making extent of each sub-expression more apparent.
The decorated output is produced by parsing and linearizing back the syntax
tree.


## Contributions

* We describe a novel way to implement incremental parsing by taking
advantage of lazy evaluation;

* We craft a data structure to be used in place of lists, which is more
efficient but has the same properties for laziness;

* We show a complete implementation of a parser combinator library for
incremental parsing and error correction;

* We have implemented such a system and made use of it to provide
syntax-dependent feedback in a production-quality editor.

# Polish Expressions

In order to represent partially evaluated results, we need a
representation for expressions. Following Swierstra and Hughes, we use a type
with at most one recursive position, giving it a linear structure. This is 
necessary to match the linear processing of the input in parsing algorithms.
In contrast to Swierstra however, we capture the matching
of types between functions and arguments in a GADT, instead of nested types.

~~~~
data a :< b
infixr :<

data Steps r where
    Push  :: a -> Steps r                  -> Steps (a :< r)
    App   :: (Steps ((b -> a) :< b :< r))  -> Steps (a :< r)
    Done  ::                                  Steps ()
~~~~

A value of type `Steps r` can be interpreted as a polish expression that
produces a stack of type `r`.

`Push` produces a stack with one more value than its argument. `App`
transforms the stack produced by its argument: it applies the function on the
top to the argument on the second position. `Done` produces the empty stack.

It is easy to translate from an applicative language to these polish expressions, 
and therefore syntax trees can be outputed in that form just as easily.


~~~~
data Applic a where
    (:*:) :: Applic (b -> a) -> Applic b -> Applic a
    Pure :: a -> Applic a
infixl :*:
toSteps expr = toP expr Done
  where toP :: Applic a -> (Steps r -> Steps (a,r))
        toP (f :*: x)  = App . toP f . toP x
        toP (Pure x)   = Push x
~~~~

~~~~
-- The expression `4 * (2 + 3)` in direct, applicative and polish style.
expr = Mul (Val 4) (Add (Val 2) (Val 3))
expr' = Pure Mul :*: (Pure Val :*: Pure 4) :*: (Pure Add :*: (Pure Val :*: Pure 2) :*: (Pure Val :*: Pure 3))
expr'' = App $ App $ Push Mul $ App $ Push Val $ Push 4 $ App $ App $ Push Add $ Push 2 $ App $ Push Val $ Push 3 $ Done
~~~~


The value of an expression can be evaluated as follows:

~~~~
evalR :: Steps (a :< r) -> (a, Steps r)
evalR (Push a r) = (a,r)
evalR (App s) = let (f, s') = evalR s
                    (x, s'') = evalR s'
                in (f x, s'')
~~~~

> Note that `fst . evalR . toSteps . traverse = id`.

> An alternative, which builds the whole stack (and thus requires a constructor for :<) is:

~~~~
evalR :: Steps r -> r
evalR (Push a r) = a :< evalR ss r
evalR (App s) = (\ ~(f:< (a:<r)) -> f a :< r) (evalR ss s)
~~~~

This evaluation procedure possesses the "online" property: parts of the polish
expression are demanded only if the corresponding parts of the input is
demanded. This preserves the incremental properties of lazy evaluation.

# Adding input

The polish expressions presented so far do not depend on input. We introduce
the `Suspend` constructor to fulfill this role: it expresses that the rest of
the expression can depend on the (first symbol of) the output. Using this we can
extend our applicative language with a construct to pattern match on the front
of the input, and write a (naive) parser for valid arithmetic expressions.

~~~~
data Steps s r where
    Push   :: a -> Steps s r ->                   Steps s (a :< r)
    App   :: (Steps s ((b -> a) :< b :< r)) ->   Steps s (a :< r)
    Done  ::                                     Steps s ()
    Suspend :: Steps s r -> (s -> Steps s r) ->  Steps s r


data Parser s a where
    (:*:) :: Parser s (b -> a) -> Parser s b -> Parser s a
    Pure :: a -> Parser s a
    Case :: Parser s a -> (s -> Parser s a) -> Parser s a

toP (Case nil cons) = \fut -> Suspend (toP nil fut) (\s -> fromP (toP (cons s) fut)
-- other cases unchanged
~~~~

~~~~
parseList :: Parser Char [SExpr]
parseList = Case 
   (Pure [])
   (\c -> case c of
       ')' -> Pure []
       '(' -> Pure (\arg rest -> S arg : rest ) :@: parseList :@: parseList
       c -> Pure (Atom c :) :@: parseList)
~~~~

Suspensions in a polish expression can be resolved by feeding input into it.
When facing a suspension, we pattern match on the input, and choose the
corresponding branch in the result.

~~~~
feed :: [s] -> Steps s r -> Steps s r
feed ss p = case p of
                  (Sus nil cons) -> case ss of
                      [] -> feed [] nil
                      Just (s:ss') -> feed (ss') (cons s)
                  (Push x p') -> Push x (feed ss p')
                  (App p') -> App (feed ss p')
~~~~

We can also obtain intermediate parsing results by feeding symbols one at a
time. The list of all intermediate results is constructed lazily using `scanl`.

~~~~
feedOne :: Steps s a -> s -> Steps s a
feedOne (Push x s)          ss = Push x (feedOne s ss)
feedOne (App f)            ss = App (feedOne f ss)
feedOne (Suspend nil cons) s  = cons s

partialParses = scanl feedOne
~~~~

Now, if the $n^{th}$ element of the input is changed, one can reuse the
$n^{th}$ element of the partial results list and feed it the new input's tail (from
that position).

This suffers from a major issue: partial results remain in their "polish
expression form", and reusing offers almost no benefit, because no computation is
shared beyond construction of the expression in polish form.
Fortunately, it is possible to partially evaluate prefixes of polish expressions.

The following definition performs this task by performing applications by
traversing the result and applying functions along the way.

~~~~
evalL :: Steps s a -> Steps s a
evalL (Push x r) = Push x (evalL r)
evalL (App f) = case evalL f of
                  (Push a (Push b r)) -> Push (a b) r
                  r -> App r
partialParses = scanl (\c -> evalL . feedOne c)
~~~~

This still suffers from a major drawback: as long as a function application is not
saturated, the polish expression will start with a (potentially long) prefix of the
form:

      partialsP = App $ Push v_1 $ App $ Push v_2 $  ... $ App $ Suspend nil cons

which cannot be simplified. 

> after parsing `(abcdefg` we get exactly this.

This prefix can persist until the end of the input is reached. A possible remedy is
to avoid writing expressions that lead to this sort of intermediate results, and
we will see in section [ref] how to do this in a particularly important case. This
however works only up to some point: indeed, there must always be an unsaturated
application (otherwise the result would be independent of the input). In general,
after parsing a prefix of size $n$, it is reasonable to expect a partial application
of at least depth $O(log~n), (otherwise the parser discards information).

Thus we have to use a better strategy to simplify intermediate results.
We want to avoid the cost of traversing the structure until we find a suspension
at each step. This suggests to use a zipper structure with the focus at this
suspension point.

~~~~
data Zip output where
   Zip :: RPolish stack output -> Steps stack -> Zip output

data RPolish input output where
  RPush :: a -> RPolish (a :< rest) output -> RPolish rest output
  RApp :: RPolish (b :< rest) output -> RPolish ((a -> b) :< a :< rest) output 
  RStop :: RPolish rest rest
~~~~

The data being linear, this zipper is very similar to the zipper for lists.
The part that is already visited ("on the left"), is reversed. Note that it contains
only values and applications, since we never go past a suspension.

The interesting features of this zipper are its type and its meaning.

First, we note that, while we obtained the data type for the left part by
mechanically inverting the type for polish expressions, it can be assigned
a meaning independently: it corresponds to *reverse* polish automatons.
Its indices are the types of the input and output stacks.

Second, we note that the stack produced by the polish expression
yet-to-visit ("on the right") is the stack consumed by the reverse polish
automation ("on the left").

We capture all these properties in the types by using GADTs. We can then
properly type the traversal of polish expressions as well as reduction to
a value.

# Parsing

## Disjunction

We kept the details of actual parsing out of the discussion so far. This is
for good reason: the machinery for incremental computation and reuse of partial
results is independent from it. Indeed, given any procedure to compute structured
values from a linear input of symbols, one can use the procedure described above
to transform it into an incremental algorithm.

However, the most common way to produce such structured values is by *parsing* the
input string. To support convenient parsing, we can introduce a disjunction operator,
exactly as Swierstra and Hughes do: the addition of the `Suspend` operator does not
undermine their treatment of disjunction in any way. 

> The zipper cannot go beyond an unresolved disjunction. That is OK if we assume that
> the parser has indeed online behavior. 

## Error correction

The online property requires that there is no error in the input. Indeed, the
`evalR` function *must* return a result (we want a total function!), so the
parser must a conjure up a suitable result for *any* input.

If the grammar is sufficiently permissive, no error correction in the parsing
algorithm itself is necessary. However, most interesting grammars produce
a highly structured result, and are correspondingly restrictive on the input
they accept. Augmenting the parser with error correction is therefore desirable.

We can do so by introducing an other constructor in the `Steps` type to represent
less desirable parses. The idea is that the grammar contains permissive rules,
but those are tagged as less desirable. The parsing algorithm can then maximize
the desirability of the set of rules used.

At each disjunction point, the parser will have to choose between two
alternatives. Since we want online behavior, we would like to do so by looking
ahead as few symbols as possible. We introduce a new type which represents this
"progress" information. This data structure is similar to a list where the
$n^{th}$ element contains how much we dislike to take this path after $n$ steps
of following it. The difference is that the list may end with success, failure
or suspension which indicates unknown final result.

If one looks at the tail of the structures, we know exactly how much the path is desirable.
However, as hinted before, we will look only only a few steps ahead, until we can safely
disregard one of the paths.

In order for this strategy to be efficient, we cache the progress information
in each disjunction node. 

This technique can be re-formulated as dynamic programming, where we use lazy
evaluation to automatically cut-off expansion of the search space. We first
define a full tree of possibilities: (Steps with disjunction), then we compute a
profile information that we tie to it; finally, finding the best path is a
matter of looking only at a subset of the information we constructed, using any
suitable heuristic.

> Here it's probably best to paste in the whole library.

# Getting rid of linear behavior

> This is related to "Binary random access lists" in Okasaki.

As we noted in a previous section, partial computations sometimes cannot be
performed. This is indeed a very common case: if the output we construct is a
list, then the spine of the list can only be constructed once we get hold of the
very tail of it. In particular, our system will behave very badly for a parser
that returns its input unmodified:

~~~~
identity = case_ 
~~~~

Wagner et al. recognize this issue and propose to handle the case of repetition
specially in the parsing. We choose a different approach, which relies on using
a different data structure for the output. The key insight is that the performance
problems come from the linearity of the list, but we can always use a tree whose
structure can be ignored when traversing the result.

Let us summarize the requirements we put on the data structure:

* It must provide the same laziness properties as a list: accessing
an element in the structure should not force to parse the input further than
necessary if we had used a list.

* the $n^{th}$ element in a list should not be further away than $O(log~n)$
elements from the root of the structure. In other words, if such a structure
contains a suspension in place of an element at position $n$, there will be
no more than $O(log~n)$ partial applications on the stack of the corresponding
partial result. This in turn means that the resuming cost for that partial result
will be in $O(log~n)$.

The second requirement suggests tree-like structure, and the first
requirement implies that whether the structure is empty or not can be determined
by entering only the root constructor. This suggests the following data type,
with the idea that it will be traversed in preorder.

~~~~
data Tree a  = Node a (Tree a) (Tree a)
             | Leaf
~~~~


The only choice that remains is the size of the subtrees. The specific choice
we make is not important as long as we make sure that each element is reachable
in $O(log~n)$ steps. A simple choice is have a list of complete trees with
increasing depth $k$, yielding a tree of size sizes $2^{k} - 1$. To make things
more uniform we can encode the list using the same datatype.

> picture

A complete tree of total depth $2 d$ can therefore store at least $\sum_{k=1}^d
2^{k}-1$ elements, fulfilling the second requirement.

## Quick access

A key observation is that, given the above structure, one can access an element
without pattern matching on any other node that is not the direct path to it.
This allows efficient access without loosing any property of laziness. Thus,
we can avoid the other source of inefficiencies of our implementation.

1. We can fetch the partial result that corresponds to the user change without
traversing the whole list of partial results or forcing its length to be computed.
Of course, the first time it is accessed intermediate results up to the one
we require still have to be computed.

2. The final results that the user observe will be in linear form as well. We
don't want to store them in a structure that forces the length, otherwise our
parser will be forced to process the whole input. Still, we want to access the
part corresponding to the window being viewed efficiently. Storing the results
in the same type of structure saves the day again.


# Results

We carried out development of a parser combinator library for incremental
parsing with support for error correction. We argumented that the complexity
of the parsing is linear, and that is can cost

> The full code is in Code.hs

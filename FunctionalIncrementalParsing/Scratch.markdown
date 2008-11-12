% Functional Incremental Parsing 
% Jean-Philippe Bernardy

# Abstract

In the context of an interactive application where the user observes only a
small window of the ouput (that is, one that corresponds to a small window of
the input), we show that combining lazy evaluation and caching of intermediate (partial)
results provides incremental parsing. We also introduce a general purpose,
simple data structure, to get rid of the linear complexity of lazy lists
traversals while retaining its lazy properties. Finally, we complete our 
treatment of incremental parsing in an interactive system by showing how
our parsing machinery can be improved to support error-correction.

# Introduction

(Introduce example Expr = Int | Add Expr Expr / SExpr ?)

In an interactive system, a lazy evaluation strategy provides a special form
of incremental computation: the amount of output that is demanded drives the
computation to be performed. In other words, the systems responds to incremental
movement of the potion of the output being viewed by the user (window) by
incremental computation of the intermediate structures.

This suggests that we can take advantage of lazy evaluation to implement
incremental parsing for an interactive application. Indeed, if we suppose that
the user makes changes in the input that "corresponds to" the window being
viewed, it suffices to cache partially computed results for each point in the
input, to obtain a system that responds to changes in the input irrespectively
of the total size of that input.

In this paper we show how this can be done in practice.

## Contributions

* We describe a novel way to implement incremental parsing in by taking
advantage of lazy evaluation;

* We have implemented such a system and made use of it to provide syntax-dependent
feedback in the Yi editor. For example, we give parenthesis matching information
for the Haskell language;

* We craft a data structure to be used in place of lists, which is more
efficient but has the same properies for laziness.

* (error correction)

# Polish Expressions

In order to represent partially evaluated results, we will need a
representation for expresions. Following Swierstra and Hughes, we use a type
with at most one recursive position. This gives it a linear structure, which is
necessary to match the input will be processed, as we will see in the following
sections. In contrast to Swierstra however, we use GADTs to capture the matching
of types between functions and arguments, instead of nested types.

~~~~
data a :< b = a :< b
infixr :<

data Steps r where
    Val   :: a -> Steps r                  -> Steps (a :< r)
    App   :: (Steps ((b -> a) :< b :< r))  -> Steps (a :< r)
    Done  ::                                  Steps ()
~~~~

This type can be interpreted as a polish expression that produces a given stack
of output. Val produces a stack with one more value as its argument. App
transforms the stack produced by its argument by applying the function on the
top to the argument on the second position. Done produces the empty stack.

It is easy to translate from an applicative language to these polish expressions:

~~~~
data Applic a where
    (:*:) :: Applic (b -> a) -> Applic b -> Applic a
    Pure :: a -> Applic a

toSteps expr = toP expr Done

toP :: Applic a -> (Steps r -> Steps (a,r))
toP (f :*: x)  = App . toP f . toP x
toP (Pure x)   = Val x
~~~~

The value of an expression can be evaluated as follows:

~~~~
evalR :: Steps s r -> r
evalR (Val a r) = a :< evalR ss r
evalR (App s) = (\ ~(f:< (a:<r)) -> f a :< r) (evalR ss s)
~~~~

with the "online" property: parts of the polish expression are demanded only if
the corresponding parts of the input is demanded. This provides the incremental
behaviour we want, as long as the user does not change the input.

# Adding suspensions


Indeed, the polish expresssions presented so far do not depend on input. We
introduce the `Suspend` constructor to fulfill this role: it expresses that the
rest of the expression can depend on the (first symbol of) the output. 

~~~~
data Steps s r where
    Val   :: a -> Steps s r ->                   Steps s (a :< r)
    App   :: (Steps s ((b -> a) :< b :< r)) ->   Steps s (a :< r)
    Done  ::                                     Steps s ()
    Suspend :: Steps s r -> (s -> Steps s r) ->  Steps s r


data Parser s a where
    (:*:) :: Parser s (b -> a) -> Parser s b -> Parser s a
    Pure :: a -> Parser s a
    Case :: a -> 

toP (Case nil cons) = \fut -> Suspend (toP nil fut) (\s -> fromP (toP (cons s) fut)

~~~~


We can construct intermediate parsing results by "pushing" a symbol of the input in the expression,
choosing the corresponding argument of the `Suspend` constructor. Similarly, we will take the
other argument if the end of the input is reached.

~~~~
pushOne :: Steps s a -> s -> Steps s a
pushOne (Val x s)          ss = Val x (pushOne s ss)
pushOne (App f)            ss = App (pushOne f ss)
pushOne (Suspend nil cons) s  = cons s

partialParses = scanl pushOne
~~~~

Now, if the $n^{th}$ element of the input is changed, one can reuse the
$n^{th}$ element of the `partials` list and push the new input tail in
that position.
This suffers from a major issue: partial results remain in their "polish
expression form". Reusing offers no benefit, because no computation (beyond
construction of the expression in polish form) is shared.

Fortunately, it is possible to partially evaluate prefixes of polish expressions.
The following definition performs this task naïvely:

~~~~
evalL :: Steps s a -> Steps s a
evalL (Val x r) = Val x (evalL r)
evalL (App f) = case evalL f of
                  (Val a (Val b r)) -> Val (a b) r
                  r -> App r
partialParses = scanl (\c -> evalL . pushOne c)
~~~~



However, this suffers from a major drawback.
A suspension "deep down", e.g.

      partials = f_1 (f_2 (f_3 ... (f_n \sigma_n)))

      partialsP = App $ Val v_1 $ App $ Val v_2 $  ... $ App $ Val v_n

cannot be simplified. This means that this situation can persist as long as
the suspension does not resolve to a saturation of the functions that it's
applied to.

Thus we have to use a better strategy to simplify intermediate results. Careful
examination of the simplification procedure shows that applications are always
performed around a given point of focus. We use the same technique as for lists:
use a zipper structure to keep the point of focus at the root of the data
structure. 

~~~~
data Zip output where
   Zip :: RPolish stack output -> Steps stack -> Zip output

data RPolish input output where
  RVal :: a -> RPolish (a :< rest) output -> RPolish rest output
  RApp :: RPolish (b :< rest) output -> RPolish ((a -> b) :< a :< rest) output 
  RStop :: RPolish rest rest
~~~~

As for lists, the part that is already visited ("on the left"), is reversed. In
the case of polish expressions, this is a *reverse* polish automaton.
Additionally, it takes as input the stack produced by the polish expresion
yet-to-visit ("on the right"). Again, we capture this property in the
types by using GADTs.


# Parsing

## disjunction


We kept the discussion of actual parsing out of the discussion so far. This is
for good reason: the machinery for incremental computation and reuse of partial
results is indepenent from it. Indeed, given any procedure to compute structured
values from a linear input of symbols, one can use the procedure discribed above
to transform it into an incremental algorithm.

However, the most common way to produce such structured values is by *parsing* the
input string. To support convenient parsing, we can introduce a disjunction operator,
exactly as Swierstra and Hughes do: the addition of the `Suspend` operator does not
undermine their treatment of disjunction in any way.

## Error correction

The online property requires that there is no error in the input. *fill*

This is a reasonable assumption if the grammar is sufficiently permissive,
but tends to conflict with the goal of yielding highly structured result.

We can however introduce a relatively simple error correction procedure in
our algorithm. *fill*



# Getting rid of linear behaviour

As we noted in a previous section, partial computations sometimes cannot be
performed. This is indeed a very common case: if the output we construct is a
list, then the spine of the list can only be constructed once we get hold of the
very tail of it. In particular, our system will behave very badly for a parser
that returns its input umodified:

~~~~
identity = case_ 
~~~~


Wagner et al. recognize this issue and propose to handle the case of repetition
specially in the parsing. We choose a different approach, which relies on using
a different data structure for the output. The key insight is that the performance
problems come from the linearity of the list, but we can always use a tree whose
structure can be ignored when traversing the result.

Let us summarize the requirements we put on the data structure:

* It must provide the same laziness properties as a list: accessing the
an element in the structure should not force to parse the input further than
necessary if we had used a list.

* the $n^{th}$ element in a list should not be further away than $O(log~n)$
elements from the root of the structure. In other words, if such a structure
contains a suspension in place of an element at position $n$, there will be
no more than $O(log~n)$ partial applications on the stack of the corresponding
partial result. This in turn means that the resuming cost for that partial result
will be in $O(log~n)$.

The second requirement suggests are tree-like structure, and the first
requirement implies that whether the structure is empty or not can be determined
by entering only the root constructor. This suggests the following data type.

~~~~
data Tree a = Node a (Tree a) (Tree a)
            | Leaf
~~~~

The only choice that remains is the size of the subtrees. There are
many possible choices here, so we chose simple rules:

1. Each node will be assigned a 'maximum size'. If the input contains
enough elements, then the size of the subtree will be its maximum size.

2. Let us define $leftSize$ to be the maximum size of the left subtree of a node.
We assign $leftSize$ for each subtree by the following recusive rule: 
    - $leftSize$ of a left child is $1$.
    - $leftSize$ of a right child is twice the $leftSize$ of the node.

3. The above rule leaves the maximum size for the whole tree undefined, but we
know that it must be unbounded to be able to store arbitrary number of elements.



> Can we prove that the requirements are fulfilled?

~~~~
direct :: Int -> [a] -> Tree a
direct leftSize [] = Leaf
direct leftSize (x:xs) = Node x (direct initialLeftSize xl)
                                (direct (leftSize * factor) xr)
  where (xl, xr) = splitAt leftSize xs
~~~~


~~~~
(.!) = look initialLeftSize
look :: Int -> Tree a -> Int -> a
look leftsize Leaf index  = error "online tree: index out of bounds"
look leftsize (Node x l r) index 
    | index == 0 = x
    | index <= leftsize = look initialLeftSize l (index - 1)
    | otherwise = look (leftsize * factor) r (index - 1 - leftsize)
~~~~

    





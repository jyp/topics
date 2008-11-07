% Functional Incremental Parsing 
% Jean-Philippe Bernardy

# Abstract

In the context of an interactive application where the user observes only a
small window of the ouput (that is, one that corresponds to a small window of
the input), we can combine lazy evaluation and caching of intermediate (partial)
results to provide incremental parsing. We also introduce a general purpose,
simple data structure, to get rid of the linear complexity of lazy lists
traversals while retaining its lazy properties.

# Introduction

In an interactive system, the lazy evaluation strategy provides a special form of
incremental computation: the amount of output that is demanded drives the
computation to be performed. In other words, the systems responds to incremental
movement of the potion of the output being viewed (window) by incremental 
computation of the intermediate structures.

This suggests we can take advantage of the lazy evaluation strategy to
implement incremental parsing for an interactive application. Indeed, if we
suppose that the user makes changes in the input that "corresponds to" the
window being viewed, it suffices to cache partially computed results for each
point in the input, to obtain a system that responds to changes in the input
irrespectively of the total size of that input.

In this paper we show how this can be done in practice.

## Contributions

* We describe a novel way to implement incremental parsing in 
by taking advantage of lazy evaluation.

* We have implemented such a system and made use of it to provide syntax-dependent
feedback in the Yi editor. For example, we give parenthesis matching information
for the Haskell language.


# Polish Expressions

In order to represent partially evaluated results, we will need a
representation for expresions. Following Swierstra and Hughes, we use a type
with at most one recursive position. This gives it a linear structure, which is
necessary to match the input will be processed, as we will see in the following
sections.

This type can be interpreted as a polish expression that produces a given stack
of output. Val produces a stack with one more value as its argument. App
transforms the stack produced by its argument by applying the function on the
top to the argument on the second position. Done produces the empty stack.

It's easy to translate from an applicative language to these polish expressions:

     code

The value of an expression can be evaluated as follows:

     evalR

with the "online" property: the part of the polish expression will be demanded
only if the corresponding part of the input is demanded.
This will provide the incremental behaviour we want, as long as the user does not
change the input.

# Adding suspensions


Indeed, the polish expresssions presented so far do not depend on input. We
introduce the |Suspend| constructor to fulfill this role: it expresses that the
rest of the expression depends on the first symbol of the output.

    Suspend :: ...

We can construct intermediate parsing results by applying the input to the
argument of the Suspend constructor. 

     push = 

     partials = scanl automaton push input

Now, if the $n^{th}$ element of the input is changed, one can reuse the
$n^{th}$ element of the |partials| list and push the new input tail in
.
This suffers from a major issue: partial results remain in their "polish
expression form". Reusing offers no benefit, because no computation (beyond
construction of the expression in polish form) is shared.

Fortunately, it is possible to partially evaluate prefixes of polish expressions.
The following definition performs this task naïvely:

    evalL = 


However, this suffers from a major drawback.
A suspension "deep down", e.g.

      partials = f_1 (f_2 (f_3 ... (f_n \sigma_n)))

      partialsP = App $ Val v_1 $ App $ Val v_2 $  ... $ App $ Val v_n

cannot be simplified. This means that, this situation can persist as long as
the suspension does not resolve to a saturation of the functions that it's
applied to.

Thus we have to use a better strategy to simplify intermediate results. Careful
examination of the simplification procedure shows that applications are always
performed around a given point of focus. This suggest that we can use a zipper-like
structure. The zipper for polish expressions has an interesting structure:

    code


It turns out that the part "on the left" is a *reverse* polish automaton, which
takes as input the stack produced by the polish expresion yet-to-visit.


# Parsing

## disjunction


We kept the discussion of actual parsing out of the discussion for good reason:
the machinery for incremental computation and reuse of partial results is
indepenent from it. Indeed, given any procedure to compute structured values
from a linear input of symbols, one can use the procedure discribed above to
transform it into an incremental algorithm.

However, the most common way to produce such structured values is by *parsing* the
input string. To support convenient parsing, we can introduce a disjunction operator,
exactly as Swierstra and Hughes do: the addition of the Suspend operator does not
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
that does not modify its input:

    code example


Wagner et al. recognize this issue and propose to handle the case of repetition
specially in the parsing. We choose a different approach, which relies on using
a different data structure for the output. 

Let us summarize the requirements we put on the data structure:

* is as lazy as a list: indeed, accessing the an element in the structure
should not force to parse the input further than necessary if we had used a
list. 

* the $n^{th}$ element in the list should not be further away than $O(log~n)$
elements from the root of the structure. In other words, if such a structure
contains a suspension in place of an element at position $n$, there will be
no more than $O(log~n)$ partial applications on the stack of the corresponding
partial result. This in turn means that the resuming cost for that partial result
will be in $O(log~n)$.

The second requirement suggests are tree-like structure, and the first
requirement suggests the following data type:

    code + comment



    





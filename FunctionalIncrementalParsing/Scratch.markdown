

# Abstract

In the context of an interactive application where the user observes only a
small window of the ouput (that is, one that corresponds to a small window of
the input), we can combine lazy evaluation and caching of intermediate (partial)
results to provide incremental parsing. We also introduce a general purpose,
simple data structure, to get rid of the linear complexity of lazy lists
traversals while retaining its lazy properties.

# Introduction

Incremental computation tackles ◌.

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
representation for for expresions. We use a "linear type" because
it matches the way the input will be processed in the later sections.


# Adding suspensions





# Abstract

In the context of an interactive application where the user observes
only a small window of the ouput (that is, one that corresponds to a small
window of the input), we can combine lazy evaluation and caching of intermediate
(partial) results to provide the equivalent of incremental computation. We also
introduce a general purpose, simple data structure, to get rid of the linear
complexity behaviour of lazy lists while retaining its lazy properties.

# Introduction

Incremental computation tackles ◌.

In an interactive system, lazy evaluation strategy provides a limited form of
incremental computation: one that depends on amount of output demanded instead
of actual changes in the input. In some sense, the factor that changes is the
portion of the output (window) that is observed. 

This suggests we can take advantage of the lazy evaluation strategy to
implement incremental computation in an interactive application. Indeed, if we
suppose that the user makes changes in the input that "corresponds to" the
window that it is viewing (We make the additional hypothesis that the function
is "quasi linear"), it suffices to cache partially computed results for each
point in the input, to obtain a system that responds to changes in the input
irrespectively of the total size of that input.



# 
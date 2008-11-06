% Functional Incremental Computation
% Jean-Philippe Bernardy

Questions: can we use function composition?

# Introduction

Problem we solve:

function $f$: [i] -> [o]

it has linear inputs and ouputs; (this is a very common case because the user
interacts linearly.)

Incremental modifications of input should incur incremental re-computations of
the output.

Additional hypothesis:
  * the user observes a small portion of the output at a time (window)
  * the window moves by small steps.
  * (the function is not cahotic (e.g. not sort))


## Outline

* Lazy evaluation solves half of the problem
* Solving the other half
  * evaluating and caching partial results 
  * get rid of inefficiencies due to naive usage of linear structures

# Representing online computations: polish expressions

# Polish expressions with suspensions

# Efficient evaluation of intermediate states: Zipping through polish expressions

# Getting rid of linear operations

## Directly jumping at the correct place in the output
## Efficient representation of output
## Directly jumping at the correct position in the cached states
## Efficient representation of intermediate structures

# Related work

* Polish parsers
* Attribute grammars
:   Attribute grammars are best suited for synthesis of information; our system to create it.
* Carlsson's recomputations
* All the incremental computing stuff

# Conclusion


Advantages: the user code does not need to specify caching points; caching points are dependent on the input.

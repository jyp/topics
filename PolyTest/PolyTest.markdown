% Testing polymorphic functions
% JP Bernardy

\DeclareUnicodeCharacter{9733}{\ensuremath{\star}} 

# Approaches

* Picking a small type (1, 2, ...)
* Picking a random type (growing) (This is what QC does!)
* Picking the minimal μ type such that  $correct (f μ) ⇒ ∀ a ∈ ★. correct (f a)$

# The Big result

## Restriction

In order to clearly identify the type we work on, we propose to verify propositions of the form:

$f x = g x$

That is, `f` is the function to check and `g` is the specification we want to check against.

I conjecture that the type of `f` is enough to infer a (minimal) type $μ$
and to prove the theorem:

$∀ x ∈ μ. f x = g x ⇒ ∀ a ∈ ★. ∀ x ∈ a. f x = g x$


## Finding μ

> f :: (F a -> a) -> (G a -> X) -> (a | X)

It suffices to test `f In`, which is monomorphic.

> f In :: (G (Fix F) -> X) -> (Fix F | X)

where

> data Fix f = In { out :: f (Fix f)}

## Proof

This is a very sketchy proof! I'm not even using the above type, but I think
this is general enough. Also, I'm taking lots of liberties with notations, etc.

Given:

> f :: (F a → a) → X → H a

Parametricity yields: (I'm using parametricity in "arrow form"; see Parametricity.markdown)

f = ⟨ (F a → a) → X → H a ⟩ f

We rewrite the relation as it's usual when using parametricity:

p = ⟨F a → a⟩ q ⇒  f p x = ⟨ H a ⟩ f q x

(i = ⟨F a⟩ j ⇒  p i = ⟨a⟩ q j) ⇒  f p x = ⟨H a⟩ f q x

(i = (F ⟨a⟩) j ⇒  p i = ⟨a⟩ q j) ⇒  f p x = (H ⟨a⟩) f q x

(p ((F ⟨a⟩) j) = ⟨a⟩ (q j)) ⇒  f p x = (H ⟨a⟩) f q x

picking q = initial F-algebra (ι) ensures that
1. ⟨a⟩ is a function and
2. the lhs. of the implication is verified.


We obtain:

∀ p x. ∃ ⟨a⟩. f p x = (H ⟨a⟩) f ι x

And we can use this to prove the result:

∀ x. f ι x = g ι x

⇒   *f is a function*

∀ x. (H ⟨a⟩) f ι x = (H ⟨a⟩) g ι x 

⇒   *by the above*

∀ p x. f p x = g p x




# Examples

> length :: [a] → Int
> filter :: (a → Bool) → [a] → [a]
> map :: (a → b) → [a] → [b]
> foldr :: (a → b → b) → b → [a] → b
> sort :: ((a × a) → Bool) → [a] → [a]

> sort :: ((a × a) → (a × a)) → [a] → [a]

For this one we get $μ = T$

> data Tree = Min (a,a) | Max (a,a) | Ix Nat

and test:

> sort (\p -> (Min p, Max p)) 

on inputs of the form 

> map Ix [1..n]

Running the this "initial" sort function then yields a representation of the sorting network.

Can we do better? 

Instead of the the initial algebra, we can use the (free) lattice algebra.

That is, we want to take the alebgra modulo these laws (the quotient space):

$min (a,max(y,z)) = max (min (a,y), min(a,z))$
$min (a,a) = a$
$max (a,a) = a$
$max (a,min(y,z)) = min (max (a,y), max(a,z))$
$min (x,min(y,z)) = min (min(x,y),z)$
$min (x,y) = min (y,x)$

""We should be able to use the free latice, but I do not understand it""

~~~~
type MinMax = [Set Int]


mmin a b = simpl (a ++ b)

mmax :: MinMax -> MinMax -> MinMax
mmax a b = simpl [x `S.union` y | x <- a, y <- b ]

simpl' [] = []
simpl' (s:ss) = s : simpl' (filter (not . (s `S.isSubsetOf`)) ss)

simpl = simpl' . sortBy (compare `on` S.size)
~~~~

Using this we can test a given length in polynomial time. 
(Because mix/max are polynomial, and because a sort normally has polynomial number of swaps)

Note that this is already better than using Knuth's result and using Bool for
'a', because the number of tests for a given list length is $2^n$. (The drawback
is that we are "forced" to run the whole thing... Unless we use laziness or
other tricks -- like using an even more restricted algebra that will test a
necessary condition for correctness)


# Effects on quickCheck, smallCheck, lazy smallCheck, EasyCheck, ...



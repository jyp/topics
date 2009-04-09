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


# Examples

> length :: [a] -> Int
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

Can we do better? It's enough if we test:

> \(f :: Nat -> Bool) -> sort (\(x,y) -> if f x <= f y then (x,y) else (y,x))

on inputs of the form

> map [1..n]

Why can we do this? 
We want to take the alebgra modulo these laws:

$min (a,max(y,z)) = max (min (a,y), min(a,z))$
$min (a,a) = a$
$max (a,a) = a$
$max (a,min(y,z)) = min (max (a,y), max(a,z))$
$min (x,min(y,z)) = min (min(x,y),z)$
$min (x,y) = min (y,x)$

> \(f :: Nat -> Bool) -> sort (\(x,y) -> if f x <= f y then (x,y) else (y,x))


> (\p -> (L p, R p)) 

# Effects on quickCheck, smallCheck, lazy smallCheck, EasyCheck, ...



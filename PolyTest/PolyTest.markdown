% Testing polymorphic functions
% JP Bernardy

\DeclareUnicodeCharacter{9733}{\ensuremath{\star}} 

# Approaches

* Picking a small type (1, 2, ...)
* Picking a random type (growing) (This is what QC does!)
* Picking the minimal μ type such that  $correct (f μ) ⇒ ∀ a ∈ ★. correct (f a)$

# Initial testing

## Theorem:

Given $f,g : ∀ a : ★. (F a → a) -> (G a → X) → H a$

Let I = fixpoint of F, and α the initial F-algebra.



∀ s : G I → X, α : F I → I.                             f α s            =        g α s

⇒ 

∀ a : ★, p : F a → a, r : G a → X.                                 f p r = g p r


This theorem says that, given a `f` is the function to check and `g`, the model we want to check against,
it suffices to test the correspondance for the inital algebra.

## Haskell

This theorem translates directly in haskell terms as follows:

> f,g :: (f a -> a) -> (g a -> X) -> g a

It suffices to test `f In`, which is monomorphic:

> f In :: (G (Fix F) -> X) -> H (Fix F)

where

> data Fix f = In { out :: f (Fix f)}


## Proof 

Given:

> f :: (F a → a) → (G a → X) → H a


Parametricity: (I'm using parametricity in "arrow form"; see Parametricity.markdown)

f = ⟨(F a → a) → (G a → X) → H a⟩ f

We rewrite the relation as usual when using parametricity:

p = ⟨F a → a⟩ q     ⇒  r = ⟨G a → X⟩ s     ⇒ f p r = ⟨H a⟩ (f q s)

p ∘ ⟨F a⟩ = ⟨a⟩ ∘ q ⇒  r ∘ ⟨G a⟩ = ⟨X⟩ ∘ s ⇒ f p r = ⟨H a⟩ (f q s)

p ∘ ⟨F a⟩ = ⟨a⟩ ∘ q ⇒  r ∘ ⟨G a⟩ =       s ⇒ f p r = ⟨H a⟩ (f q s)

p ∘ ⟨F a⟩ = ⟨a⟩ ∘ q                       ⇒ f p r = ⟨H a⟩ (f q (r ∘ ⟨G a⟩))

p ∘ F ⟨a⟩ = ⟨a⟩ ∘ q                       ⇒ f p r = H ⟨a⟩ (f q (r ∘ G ⟨a⟩))


Satisfying the premise is equivalent to make this diagram commute:

\begin{tikzpicture}[->,auto,node distance=2.8cm, semithick]
  \tikzstyle{object}=[]

  \node[object]         (A)                    {$t$};
  \node[object]         (B) [left of=A] {$F~t$};
  \node[object]         (C) [below of=A] {$a$};
  \node[object]         (D) [below of=B] {$F~a$};

  \path (B) edge              node {$q$} (A)
        (A) edge              node {$⟨a⟩$}   (C);

  \path (B) edge              node {$F ⟨a⟩$} (D)
        (D) edge              node {$p$}     (C);
        
\end{tikzpicture}


This can be achieve by picking

* q = α, the initial F-algebra
* ⟨a⟩ = ⦃p⦄, p's catamorphism.
* t = I = Fix F

This choice implies that:

1. the lhs. of the implication is verified;
2. $⟨a⟩ = ⦃p⦄$ is an function, of type $I → a$.


We obtain equation (1): 

∀ a : ★, p : F a → a, r : a → X. f p r = H ⦃p⦄ (f α (r ∘ G ⦃p⦄))

And we can use this to prove the result:

∀ s : G I → X, α : F I → I.                             f α s            =        g α s

⇒   *∀ p : F a → a, r : G a → X. r ∘ G ⦃p⦄ : I → X*

∀ a : ★, p : F a → a, r : G a → X.                      f α (r ∘ G ⦃p⦄)  =        g α (r ∘ G ⦃p⦄)

⇒   *$⦃p⦄$ is a function*

∀ a : ★, p : F a → a, r : G a → X.               H ⦃p⦄ (f α (r ∘ G ⦃p⦄)) = H ⦃p⦄ (g α (r ∘ G ⦃p⦄))

⇒   *by (1)*

∀ a : ★, p : F a → a, r : G a → X.                                 f p r = g p r


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

That is, we want to take the alebgra modulo distributive lattice laws:

$min (a,max(y,z)) = max (min (a,y), min(a,z))$
$min (a,a) = a$
$max (a,a) = a$
$max (a,min(y,z)) = min (max (a,y), max(a,z))$
$min (x,min(y,z)) = min (min(x,y),z)$
$min (x,y) = min (y,x)$

I.e. the minimal type is the free distributive lattice.

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



# Applying the result

The result can be readily applyied to functions of the form (...), it is rare that functions 
exactly fix it.

However, many functions can be transformed to fix the model, and the result can
be re-interpreted directly on their initial form.




> (a → Bool) → [a] → [a]

list morphism

> (a → Bool) → (Nat × (Nat → a)) → (Nat × (Nat → a))

ignoring the parameter for the 1st component in the tuple

> (a → Bool) → (Nat × (Nat → a)) → Nat → (a × Nat) 

→-normal form

> (a → Bool) → Nat → (Nat → a) → Nat → (a × Nat) 

reordering 

> (Nat → a) → (a → Bool) → Nat → Nat → (a × Nat) 

ignoring monomorphic arguments

> (Nat → a) → (a → Bool) → (a × Nat) 

rewriting as functors

> (K Nat → a) → (a → Bool) → (Id × K Nat) a




> [a] → Nat 

> (Nat × (Nat → a)) → Nat 



# Effects on quickCheck, smallCheck, lazy smallCheck, EasyCheck, ...

A parameter that used to be "sampled" becomes fixed. Work is moved from the
generation of many test cases to checking against the model. We can simplify
this work by taking advantage of laws that the free algebra must satisfy.


# Limitations

* Order 3 polymorphism?
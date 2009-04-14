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

That is, `f` is the function to check and `g` is the model we want to check against.

I conjecture that the type of `f` is enough to infer a (minimal) type $μ$
and to prove the theorem:

$∀ x ∈ μ. f x = g x ⇒ ∀ a ∈ ★. ∀ x ∈ a. f x = g x$


## Finding μ

> f :: (F a -> a) -> (G a -> X) -> H a

It suffices to test `f In`, which is monomorphic:

> f In :: (G (Fix F) -> X) -> H (Fix F)

where

> data Fix f = In { out :: f (Fix f)}


## Proof 

This is a very sketchy proof! I'm taking lots of liberties with notations, etc.

Given:

> f :: (F a → a) → (a → X) → H a

Parametricity: (I'm using parametricity in "arrow form"; see Parametricity.markdown)

f = ⟨(F a → a) → (a → X) → H a⟩ f

We rewrite the relation as usual when using parametricity:

p = ⟨F a → a⟩ q     ⇒  r = ⟨a → X⟩ s     ⇒ f p r = ⟨H a⟩ (f q s)

p ∘ ⟨F a⟩ = ⟨a⟩ ∘ q ⇒  r ∘ ⟨a⟩ = ⟨X⟩ ∘ s ⇒ f p r = ⟨H a⟩ (f q s)

p ∘ ⟨F a⟩ = ⟨a⟩ ∘ q ⇒  r ∘ ⟨a⟩ =       s ⇒ f p r = ⟨H a⟩ (f q s)

p ∘ ⟨F a⟩ = ⟨a⟩ ∘ q                      ⇒ f p r = ⟨H a⟩ (f q (r ∘ ⟨a⟩))

p ∘ F ⟨a⟩ = ⟨a⟩ ∘ q                      ⇒ f p r = H ⟨a⟩ (f q (r ∘ ⟨a⟩))


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


picking 

* t = I = Fix F
* q = ι the initial F-algebra

ensures that

1. for all $a$, $⟨a⟩$ is the unique arrow of type $I → a$;
2. the lhs. of the implication is verified;
3. $⟨a⟩$ is a function.


We obtain equation (1): 

∀ a : ★, p : F a → a, r : a → X. f p r = H ⟨a⟩  (f ι (r ∘ ⟨a⟩))

And we can use this to prove the result:

∀ s : I → X. f ι s = g ι s

⇒   *by the lemma 1, we can rewrite $s$ as a composition with $⟨a⟩$*

∀ a : ★, r : a → X. f ι (r ∘ ⟨a⟩) = g ι (r ∘ ⟨a⟩)

⇒   *$⟨a⟩$ is a function*

∀ a : ★, r : a → X. (H ⟨a⟩) (f ι (r ∘ ⟨a⟩)) = (H ⟨a⟩) (g ι (r ∘ ⟨a⟩))

⇒   *by (1)*

∀ a : ★, p : F a → a, r : a → X. f p r = g p r

### Lemma 1

Let 

* $I$ be the initial object
* $s : I → X$
* $r : A → X$
* $r ∘ x = s$

then $x$ is the unique arrow $x : I → a$


\begin{tikzpicture}[->,auto,node distance=2.8cm,
                    semithick]
  \tikzstyle{object}=[]

  \node[object]         (I)                   {$I$};
  \node[object]         (A) [right of=I]      {$a$};
  \node[object]         (X) [right of=A]      {$X$};

  \path (I) edge [bend left]  node {$s$} (X);
  \path (A) edge              node {$r$} (X);
  \path (I) edge              node {$x$} (A);

        
\end{tikzpicture}



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

# Effects on quickCheck, smallCheck, lazy smallCheck, EasyCheck, ...

A parameter that used to be "sampled" becomes fixed. Work is moved from the
generation of many test cases to checking against the model. We can simplify
this work by taking advantage of laws that the free algebra must satisfy.



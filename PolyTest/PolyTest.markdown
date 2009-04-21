% Testing polymorphic functions
% JP Bernardy

\newcommand{\lbana}{\mbox{$(\![$}}
\newcommand{\rbana}{\mbox{$]\!)$}}
\newcommand{\cata}[1]{\mbox{$\lbana #1 \rbana$}}

\DeclareUnicodeCharacter{9733}{\ensuremath{\star}} 
\DeclareUnicodeCharacter{8614}{\ensuremath{\mapsto}}
\DeclareUnicodeCharacter{10627}{\ensuremath{\lbana}} 
\DeclareUnicodeCharacter{10628}{\ensuremath{\rbana}} 


# Intro

Testing lends itself well to concrete functions. Polymorphic (higher order) functions are
more abstract and are often considered easy to proove correct: testing is less
useful. Thanks to parametricity, there is often only one possible implementation
for "very polymorphic" functions. If types are considered theorems, the
computational content of the values is often irrelevant.

We attack the middle ground where there is little polymorphism, but there is
still a possibility to get it wrong; and doing a proof is still more tedious than
performing a simple test.

Introduce the running example here.

# Picking a type

Testing a polymorphic function is often considered "not possible" . For example, 
QuickCheck simply requires monomorphic properties. One must first instanciate the
type parameters to concrete types. Here, multiple approaches spring to mind:

* Picking a small type (1, 2, ...)
* Picking a random type (growing) (This is what QC does!)
* Picking the minimal μ type such that  $correct (f μ) ⇒ ∀ a ∈ ★. correct (f a)$

# Initial testing

## Theorem:

Given $f,g : ∀ a : ★. (F a → a) → (G a → X) → H a$

Let I = fixpoint of F, and α the initial F-algebra.



∀ s : G I → X, α : F I → I.                             f α s            =        g α s

⇒ 

∀ a : ★, p : F a → a, r : G a → X.                                 f p r = g p r


This theorem says that, given `f`, the function to check and `g`, the model we
want to check against, it suffices to test the correspondance for the inital
F-algebra.

## Haskell

This theorem translates directly in Haskell terms as follows:

Given:

> f,g :: (F a -> a) -> (G a -> X) -> H a
> data Fix f = In { out :: f (Fix f) }

It suffices to test `f In`, which is monomorphic:

> f In :: (G (Fix F) -> X) -> H (Fix F)


## Proof 

f : ∀ a. (F a → a) → (G a → X) → H a

parametricity

f ⟨∀ a. (F a → a) → (G a → X) → H a⟩ f 

definition of ⟨...⟩ 

∀ t₁,t₂:★, R : t₁ ↔ t₂,      $f_{t₁} ⟨(F a → a) → (G a → X) → H a⟩_{a ↦ R} f_{t₂}$

in particular, we can restrict ρ to be a function:

∀ t₁,t₂:★, ρ : t₁ → t₂,      $f_{t₁} ⟨(F a → a) → (G a → X) → H a⟩_{a ↦ ρ} f_{t₂}$

In the following the index $⟨...⟩_{a ↦ ρ}$ is left implict (so that the propositions fit on a line)

introducing
* p: F t₁ → t₁, q : F t₂ → t₂
* r: G t₁ → X, s : G t₂ → X

$p ⟨F a → a⟩ q                                        ⇒  r ⟨G a → X⟩ s                                      ⇒ f_{t₁} p r ⟨H a⟩ (f_{t₂} q s)$

definition of ⟨...⟩ 

$(∀ x: F t₁, y : F t₂. x ⟨F a⟩ y ⇒ p x ⟨a⟩ q y)       ⇒  (∀ x: G t₁, y : G t₂. x ⟨G a⟩ y ⇒ r x ⟨X⟩ s y)     ⇒ f_{t₁} p r ⟨H a⟩ (f_{t₂} q s)$

using ⟨a⟩ = ρ, a function:

$(∀ x: F t₁, y : F t₂. x = F ρ y ⇒ p x = ρ (q y))     ⇒  (∀ x: G t₁, y : G t₂. x = G ρ y ⇒ r x  =  s y)     ⇒ f_{t₁} p r = H ρ (f_{t₂} q s)$

substitutions

$(∀ y: F t₂.                 p (F ρ y) = ρ (q y))     ⇒  (∀ y : G t₂.           r (G ρ y) = s y)            ⇒ f_{t₁} p r = H ρ (f_{t₂} q s)$

definition of function composition

$p ∘ F ρ = ρ ∘ q                                      ⇒  r ∘ G ρ = s                                        ⇒ f_{t₁} p r = H ρ (f_{t₂} q s)$

elimination of s

$p ∘ F ρ = ρ ∘ q                                                                                            ⇒ f_{t₁} p r = H ρ (f_{t₂} q (r ∘ G ρ))$




Satisfying the premise is equivalent to make this diagram commute:

\begin{tikzpicture}[->,auto,node distance=2.8cm, semithick]
  \tikzstyle{object}=[]

  \node[object]         (A)                    {$t₁$};
  \node[object]         (B) [left of=A] {$F~t₁$};
  \node[object]         (C) [below of=A] {$t₂$};
  \node[object]         (D) [below of=B] {$F~t₂$};

  \path (B) edge              node {$q$} (A)
        (A) edge              node {$ρ$}   (C);

  \path (B) edge              node {$F ρ$} (D)
        (D) edge              node {$p$}     (C);
        
\end{tikzpicture}


This can be achieved by picking 

* q = α, the initial F-algebra.
* ρ = ⦃p⦄, the catamorphism of p.

Thus, the lhs. of the implication is verified, and

1. t₁ = μ F
2. $⦃p⦄$ is an function, of type $μ F → a$.


We obtain equation (1) by substituting t for t₂.: 

$∀ t : ★, p : F t → t, r : G t → X. f_{t} p r = H ⦃p⦄ (f_{μ F} α (r ∘ G ⦃p⦄))$

And we can use this to prove the result:

$∀ s : G (μ F) → X, α : F (μ F) → (μ F).                             f_{μ F} α s            =        g_{μ F} α s$

⇒   *∀ p : F a → a, r : G a → X. r ∘ G ⦃p⦄ : (μ F) → X*

$∀ a : ★, p : F a → a, r : G a → X.                      f_{μ F} α (r ∘ G ⦃p⦄)  =        g_{μ F} α (r ∘ G ⦃p⦄)$

⇒   *$⦃p⦄$ is a function*

$∀ a : ★, p : F a → a, r : G a → X.               H ⦃p⦄ (f_{μ F} α (r ∘ G ⦃p⦄)) = H ⦃p⦄ (g_{μ F} α (r ∘ G ⦃p⦄))$

⇒   *by (1)*

$∀ a : ★, p : F a → a, r : G a → X.                                 f_a p r = g_a p r$


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
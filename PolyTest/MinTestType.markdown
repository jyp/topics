% Recovering the Initial Type 
% Jean-Philippe Bernardy


\DeclareUnicodeCharacter{9733}{\ensuremath{\star}} 

# Motivation

QuickCheck testing of a polymorphic function can be done by using a specific
type for each type variable.

For example, if one wishes to test

> sort :: forall a. ((a,a) -> (a,a)) -> [a] -> [a]

one can pick `Int` for `a`. If one can gain confidence that the function works for `Int`, 
it will work for any type `a`.


Picking `Int` is a waste however: it is a type with 2^32^ elements, but it would
have sufficed to use a type with $2$ elements to verify that the $sort$ function
works.

In this memo I propose a systematic technique to pick the minimal type for verifying a 
polymorphic function.



# Parametricity

The key to pick the minimal type is to use the parametricity theorem. 



# Proposition form

In order to clearly identify the type we work on, we propose to verify propositions of the form:

$f x = g x$

That is, `f` is the function to check and `g` is the specification we want to check against.

I conjecture that the type of `f` is enough to infer a (minimal) type $μ$
and to prove the theorem:

$∀ x ∈ μ. f x = g x ⇒ ∀ a ∈ ★. ∀ x ∈ a. f x = g x$

# Examples

## One

We can outline our reasoning with a trivial example:

> f :: a -> Bool

Parametricity: $∀ R ∈ (t₁ × t₂), ∀ (x,y) ∈ R, f x = f y$

Picking $t₁ = a, t₂ = (), R = \{(x,()) | x ∈ a\}$, we get 

$∀ f. f x = f ()$

Hence we can choose $μ = ()$, and the theorem is easy to prove, by equational reasoning:

$∀ x ∈ μ. f x = g x ⇒ ∀ a ∈ ★. ∀ x ∈ a. f x = g x$

applying the parametricity instance:

$∀ x ∈ μ. f x = g x ⇒ ∀ a ∈ ★. ∀ x ∈ a. f () = g ()$

$μ$ has only one inhabitant:

$∀ x ∈ μ. f () = g () ⇒ ∀ a ∈ ⋆. ∀ x ∈ a. f () = g ()$

dropping useless quantifiers:

$f () = g () ⇒ f () = g ()$

qed.


## Two

Slightly less trivial example:


> f :: (a -> Bool, a)  -> Bool

Parametricity: 

$∀ R ∈ (t₁ × t₂). ∀ ((x₁,x₂),(y₁,y₂)) ∈ \{((x₁, x₂), (y₁, y₂)) |
       (∀ (x, y) ∈ R. x₁ x = y₁ y) ∧ ((x₂, y₂) ∈ R)\}.f (x₁,x₂) = f (y₁,y₂)$

or

$∀ R ∈ (t₁ × t₂), x₁ : t₁ → Bool, y₁ t₂ → Bool, (x₂,y₂) ∈ R,
       (∀ (x, y) ∈ R. x₁ x = y₁ y) ⇒ f (x₁,x₂) = f (y₁,y₂)$


Reorder the quantifiers:

$∀ x₁ : t₁ → Bool, y₁ t₂ → Bool, R ∈ (t₁ × t₂), (x₂,y₂) ∈ R,
       (∀ (x, y) ∈ R. x₁ x = y₁ y) ⇒ f (x₁,x₂) = f (y₁,y₂)$


Let's choose $R = \{(x,y) | x₁ x = y₁ y\}$

$∀ x₁ : t₁ → Bool, y₁ : t₂ → Bool, (x₂,y₂) ∈ R,
       (∀ (x, y) ∈ R. x₁ x = y₁ y) ⇒ f (x₁,x₂) = f (y₁,y₂)$

The premise can be dropped by definition of $R$.

$∀ x₁ : t₁ → Bool, y₁ : t₂ → Bool, (x₂,y₂) ∈ R, f (x₁,x₂) = f (y₁,y₂)$

Unfolding $R$:

$∀ x₁ : t₁ → Bool, y₁ : t₂ → Bool, (x₂,y₂) ∈ \{(x,y) | x₁ x = y₁ y\}, f (x₁,x₂) = f (y₁,y₂)$


(Intuitively, we want to pick t_2 such that y_1 is the initial algebra for it.)

Picking

  * $y₁$ = $id$
  * $t₂$ = Bool


We obtain:

$∀ x₁ : t₁ → Bool, (x₂,y₂) ∈ \{(x,y) | x₁ x = y\}, f (x₁,x₂) = f (id,y₂)$

and:

$∀ x₁ : t₁ → Bool, x₂ ∈ t₁,y₂ ∈ Bool,  x₁ x₂ = y₂ ⇒ f (x₁,x₂) = f (id,y₂)$

subtituting y₂

$∀ x₁ : t₁ → Bool, x₂ ∈ t₁, f (x₁,x₂) = f (id,x₁ x₂)$

So, we have $μ = \{id\} × Bool$

Again, we can prove the theorem by equational reasoning:

$∀ x ∈ μ. f x = g x ⇒ ∀ a ∈ ★. ∀ x ∈ a. f x = g x$

Unfolding $μ$:

$∀ x₂ ∈ Bool. f (id,x₂) = g (id,x₂) ⇒ ∀ a ∈ ★. ∀ (x₁,x₂) ∈ a. f (x₁,x₂) = g (x₁,x₂)$

applying the parametricity instance:

$∀ x₂ ∈ Bool. f (id,x₂) = g (id,x₂) ⇒ ∀ a ∈ ★. ∀ (x₁,x₂) ∈ a. f (id,x₁ x₂) = g (id,x₁ x₂)$

observing that $x₁ x₂ ∈ Bool$, we can conclude.

qed.


## Three

Slightly less trivial example again:


> f :: (a -> Bool, a -> Bool, a)  -> Bool

Parametricity: 

$∀ R ∈ (t₁ × t₂). ∀ ((x₁,x₂,x₃),(y₁,y₂,y₃)) ∈ \{((x₁, x₂, y₃), (y₁, y₂, y₃)) |
       (∀ (x, y) ∈ R. x₁ x = y₁ y ∧ x₂ x = y₂ y) ∧ ((x₃, y₃) ∈ R)\}.f (x₁,x₂,x₃) = f (y₁,y₂,y₃)$

or

$∀ R ∈ (t₁ × t₂), x₁,x₂ : t₁ → Bool, y₁,y₂ : t₂ → Bool, (x₃,y₃) ∈ R,
       (∀ (x,y) ∈ R. x₁ x = y₁ y ∧ x₂ x = y₂ y) ⇒ f (x₁,x₂,x₃) = f (y₁,y₂,y₃)$


Reorder the quantifiers:

$∀ x₁,x₂ : t₁ → Bool, y₁,y₂ : t₂ → Bool, R ∈ (t₁ × t₂), (x₃,y₃) ∈ R,
       (∀ (x,y) ∈ R. x₁ x = y₁ y ∧ x₂ x = y₂ y) ⇒ f (x₁,x₂,x₃) = f (y₁,y₂,y₃)$



Let's choose $R = \{(x,y) | x₁ x = y₁ y ∧ x₂ x = y₂ y\}$


The premise can be dropped by definition of $R$.

$∀ x₁,x₂ : t₁ → Bool, y₁,y₂ : t₂ → Bool, (x₃,y₃) ∈ R,
       f (x₁,x₂,x₃) = f (y₁,y₂,y₃)$


Unfolding $R$:

$∀ x₁,x₂ : t₁ → Bool, y₁,y₂ : t₂ → Bool, (x₃,y₃) ∈ \{(x,y) | x₁ x = y₁ y ∧ x₂ x = y₂ y\},
       f (x₁,x₂,x₃) = f (y₁,y₂,y₃)$



(Intuitively, we want to pick $t_2$ such that $y_1$, $y_2$ is the initial algebra for it.)

Picking

  * $y₁$ = $fst$
  * $y₂$ = $snd$
  * $t₂$ = (Bool × Bool)


We obtain:

$∀ x₁ : t₁ → Bool, (x₃,y₃) ∈ \{(x,y) | x₁ x = fst y ∧ x₂ x = snd y\}, f (x₁,x₂,x₃) = f (fst,snd,y₃)$

and:

$∀ x₁ : t₁ → Bool, x₃ ∈ t₁, y₃ ∈ (Bool × Bool), x₁ x₃ = fst y₃ ∧ x₂ x₃ = snd y₃ ⇒ f (x₁,x₂,x₃) = f (fst,snd,y₃)$

let $y₃ = (x₁ x₃, x₂ x₃)$

$∀ x₁ : t₁ → Bool, x₃ ∈ t₁, y₃ ∈ (Bool × Bool), f (x₁,x₂,x₃) = f (fst,snd,(x₁ x₃, x₂ x₃))$


So, we have $μ = \{fst\} × \{snd\} × Bool$

Again, we can prove the theorem by equational reasoning:

$∀ x ∈ μ. f x = g x ⇒ ∀ a ∈ ★. ∀ x ∈ a. f x = g x$

Unfolding $μ$:

$∀ x₂ ∈ Bool. f (fst,snd,x₃) = g (fst,snd,x₃) ⇒ ∀ a ∈ ★. ∀ (x₁,x₂,x₃) ∈ a. f (x₁,x₂,x₃) = g (x₁,x₂,x₃)$

applying the parametricity instance:

$∀ x₁ : t₁ → Bool, x₃ ∈ t₁, y₃ ∈ (Bool × Bool), f (x₁,x₂,x₃) = f (fst,snd,(x₁ x₃, x₂ x₃))$

$∀ x₂ ∈ Bool. f (fst,snd,x₃) = g (fst,snd,x₃) ⇒ ∀ a ∈ ★. ∀ (x₁,x₂,x₃) ∈ a. f (fst,snd,(x₁ x₃, x₂ x₃) = g (fst,snd,(x₁ x₃, x₂ x₃))$

observing that $(x₁ x₃, x₂ x₃) ∈ Bool × Bool$, we can conclude.

qed.


## Four

> f :: a -> a


$∀ R ∈ (t₁ ↔ t₂). ∀ x,y. (x ⟨R⟩ y ⇒ f x ⟨R⟩ f y)


Let's choose $R = \{(x,z) | x ∈ a\}$ (constant function)

Using R:

$∀ z,x,y. (x = z ⇒ f x = z)$

or

$∀ z. f z = z$

we can pick any μ, and there is nothing to prove.

## Five

> f :: (a -> Bool, a) -> a

Parametricity: 


$∀ R ∈ (t₁ ↔ t₂). ∀ ((p,x),(q,y)). (∀a,b. a R b ⇒ p a = q b) ⇒ x R y ⇒ (f p x) R (f q y)$


Let's choose $R = \{(x,z) | x ∈ a\}$ (constant function)


$∀ z. ∀ ((p,x),(q,y)). (∀a,b. a = z ⇒ p a = q b) ⇒ x = z ⇒ f p x = z$

or 

$∀ z. ∀ ((p,x),(q,y)). (∀b. p z = q b) ⇒ f p z = z$

let $q _ = p z$

$∀ z. ∀ ((p,x),(q,y)). (∀b. p z = q b) ⇒ f p z = z$

then

$∀ z p. f p z = z$

we can pick any μ, and there is nothing to prove.



## Six

> f :: (X -> a) -> a

Parametricity: 


$f ⟨(X → a) → a⟩ f$

$p ⟨X → a⟩ q ⇒ f p ⟨a⟩ f q$

$p x ⟨a⟩ q x ⇒ f p ⟨a⟩ f q$




## More

> f :: (X -> a) -> (a -> Y) -> a
> f :: (X -> a) -> (a -> Y) -> Z
> f :: (X -> a) -> (a -> Y) -> Z -> a


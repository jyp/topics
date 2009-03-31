% Parametricity theorem Cheat Sheet
% Jean-Philippe Bernardy

\DeclareUnicodeCharacter{10214}{\ensuremath{\langle}} 
\DeclareUnicodeCharacter{10215}{\ensuremath{\rangle}} 
\DeclareUnicodeCharacter{9733}{\ensuremath{\star}} 

$⟦\_⟧ : (A : ★) → [(A,A)]$


If $t$ is a closed term of type $T$, then $(t,t) ∈ ⟦T⟧$, where


  * $⟦A⟧ = [(x,x) | x ∈ A]$
  * $⟦A × B⟧ = [((x,y),(x',y')) | (x,x') ∈ ⟦A⟧ ∧ (y,y') ∈ ⟦B⟧]$
  * List is the same stuff.
  * $⟦A → B⟧ = [(f,f') | ∀ (x,x') ∈ ⟦A⟧, (f x, f' x') ∈ ⟦B⟧]$
  * $⟦∀ X. F(X)⟧ = [(g,g') | ∀ a ∈ A ↔ A', (g_A,g'_{A'}) ∈ ⟦F(a)⟧)]$



As relations:  $⟦\_⟧ : (A : ★) → A → A → Prop$

If $t$ is a closed term of type $T$, then $t ⟦T⟧ t$, where

* x ⟦A⟧ x' = x ≡_{A} x'
* (x,y) ⟦A × B⟧ (x',y') = x ⟦A⟧ x' ∧ y ⟦B⟧ y'
* x ⟦[A]⟧ x' = x (zipWith_{A} ⟦A⟧) x'
* f ⟦A → B⟧ f' = ∀ x,x': A. x ⟦A⟧ x' ⇒ f x ⟦B⟧ f' x'
* g ⟦∀ X. F(X)⟧ g' = ∀ a : A ↔ A'. g_A ⟦F(a)⟧ g'_{A'}$
  

As relations in arrow form $⟦\_⟧ : (A : ★) → (A ↔ A)$

If $t$ is a closed term of type $T$, then $f = ⟦T⟧ f$, where

* ⟦K⟧ x = x
* ⟦A × B⟧ (x,y) = (⟦A⟧ x, ⟦B⟧ y)
* ⟦[A]⟧ x = fmap ⟦A⟧ x
* ⟦A → B⟧ f =  ⟦B⟧ ∘ f ∘ ⟦A⟧? 
* ⟦∀ X. F(X)⟧ g = ∀ a : A ↔ A'. ⟦F(a)⟧ g_{A}$
  

-- λf·






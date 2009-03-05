% Parametricity theorem Cheat Sheet
% Jean-Philippe Bernardy

\DeclareUnicodeCharacter{10214}{\ensuremath{\langle}} 
\DeclareUnicodeCharacter{10215}{\ensuremath{\rangle}} 
\DeclareUnicodeCharacter{9733}{\ensuremath{\star}} 

If $t$ is a closed term of type $T$, then (t,t) ∈ ⟦T⟧, where


  * $⟦A⟧ = [(x,x) | x ∈ A]$
  * $⟦A × B⟧ = [((x,y),(x',y')) | (x,x') ∈ ⟦A⟧ ∧ (y,y') ∈ ⟦B⟧]$
  * List is the same stuff.
  * $⟦A → B⟧ = [(f,f') | ∀ (x,x') ∈ ⟦A⟧, (f' x, f x') ∈ ⟦B⟧]$
  * $⟦∀ X. F(X)⟧ = [(g,g') | ∀ a ∈ A ↔ A', (g_A,g'_{A'}) ∈ ⟦F(A)⟧)]$



$⟦\_⟧ : (A : ★) → [(A,A)]$
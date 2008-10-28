{-# OPTIONS --type-in-type 
  #-}
-- (I take the same liberty as in the paper wrt. universe layers.)

-- This is a translated from "Parametric Higher-Order Abstract Syntax
-- for Mechanized Semantics", Adam Chlipala.


module PHOAS where

open import Data.Nat
open import Data.Bool
open import Data.Unit
open import Data.Function
open import Data.List
open import Data.Product hiding (_×_)

module ConcreteSyntax where
  -- Let's try to represent variables by they names. 
  -- This is what we do on paper!
  open import Data.String hiding (_++_)
  Symbol = String

  data Term : Set where
    Var : Symbol -> Term
    Abs : Symbol -> Term -> Term
    App : Term -> Term -> Term

  
  -- In practise substitution is quite hard though, be cause of the
  -- name-capture problem.
  postulate _`elem`_ : Symbol -> List Symbol -> Bool
  postulate addPrime : Symbol -> Symbol
  postulate freeVars : Term -> List Symbol
  postulate freshVar : List Symbol -> Symbol -> Symbol


  mutual  
    --  substitution (Lennart Augustsson)
    subst : Symbol -> Term -> Term -> Term
    subst v x b = sub b
      where fvx : List Symbol
            fvx = freeVars x
            sub : Term -> Term
            sub (Var i) = if i == v then x else Var i
            sub (App f a) = App (sub f) (sub a)
            sub (Abs i e) =
                if v == i then
                  Abs i e
                else 
                   if i `elem` fvx then
                       Abs i' (sub e')
                     else
                       Abs i (sub e)
                where i' = freshVar (freeVars e ++ fvx) i
                      e' = subst i (Var i') e
  -- Problem: introducing fresh variables. How to do it locally?


  -- Proving anything that involves substitution is a nightmare!

module DeBruijnIndices where

  data Term : Set where
    v_  : forall (n : ℕ) -> Term
    λ_  : Term -> Term
    _#_ : Term -> Term -> Term


  -- substitution (TAPL 6.2.1)
 
  ↑ : ℕ -> ℕ -> Term -> Term
  ↑ c d (v k) with compare k c
  ↑ .(suc (k + x)) d (v k) | less .k x = v k
  ... | _ = v (d + k)
  ↑ c d (λ t1) = λ (↑ (1 + c) d t1)
  ↑ c d (t1 # t2) = ↑ c d t1 # ↑ c d t2

  subst : ℕ -> Term -> Term -> Term
  subst j s (v k) with compare j k 
  subst j s (v .j)| equal .j = s
  ... | _ = v k
  subst j s (λ t1) = λ  (subst (1 + j) (↑ 0 1 s) t1)
  subst j s (y # y') = subst j s y # subst j s y'

  -- substitution is simpler, but working with this requires rewiring
  -- your brain.

module HOAS where
  -- Idea: use the λ construct of the host language to represent binding

  data Term : Set where
    App : Term -> Term -> Term
    -- Abs : (Term -> Term) -> Term -- ouch, posititity.



module PHOAS where

 module UntypedLambdaCalculus where 
 
  data Term (V : Set) : Set where 
     -- V is the type of variables
     Var : (v : V) -> Term V
     App : Term V -> Term V -> Term V
     Abs : (V -> Term V) -> Term V
  -- only variables can be bound in an abstraction, not terms
  -- (Really we were silly before!)

  -- we can define a couple of terms:  
  phoas_id : {V : Set} -> Term V
  phoas_id = Abs (\x -> Var x)

  Ω : {V : Set} -> Term V
  Ω = App (Abs (\x -> App (Var x) (Var x))) (Abs (\x -> App (Var x) (Var x)))


  -- Claim: We'll ensure that we don't store data in
  -- variables by always parameterizing on V.
  -- ie. instantiation does not incurr loss in generality.

  UsedTerm = {V : Set} -> Term V

  -- Type of terms with one free variable
  UsedTerm1 = {V : Set} -> (V -> Term V)

  -- count variable uses
  numVars : Term ⊤ -> ℕ
  numVars (Var _) = 1
  numVars (App e1 e2) = numVars e1 + numVars e2
  numVars (Abs e') = numVars (e' tt)

  nV : UsedTerm -> ℕ
  nV t = numVars t 

  -- is function a candidate for η-reduction?
  -- \v -> (term where v does not appear) v
  canEta' : Term Bool -> Bool
  canEta' (Var b) = b
  canEta' (App e1 e2) = canEta' e1 ∧ canEta' e2
  canEta' (Abs e') = canEta' (e' true)

  canEta : Term Bool -> Bool
  canEta (Abs e') with e' false 
  ... | App e1 (Var false) = canEta' e1
  ... | _ = false
  canEta _ = false

  canη : UsedTerm -> Bool
  canη t = canEta t 

  -- there is actually a mistake in the paper probably;
  -- they forget treat the top-level abstraction.

  -- The dreaded substitution with name capture...
  subst : {V : Set} -> Term (Term V) ->  Term V
  subst (Var e) = e
  subst (App e1 e2) = App (subst e1) (subst e2)
  subst (Abs e') = Abs (\x -> subst (e' (Var x))) 
  -- turns out very easy.
  -- (cleverness: nest terms!)


  subst' : UsedTerm1 -> UsedTerm -> UsedTerm
  subst' e1 e2 {V} = subst ((e1 {Term V}) (e2 {V}))

 module SimplyTypedLambdaCalculus where

  data Type : Set where 
     Boo : Type
     Arr : Type -> Type -> Type

  ⟦_⟧ : Type -> Set 
  ⟦ Boo ⟧ = Bool
  ⟦ Arr τ τ' ⟧ = ⟦ τ ⟧ -> ⟦ τ' ⟧

  -- Terms, with additional Type index.
  data Term (V : Type -> Set) : (τ : Type) -> Set where 
     Tru : Term V Boo
     Fals : Term V Boo
     Var : {τ : Type} -> (v : V τ) -> Term V τ
     App : {τ1 τ2 : Type} -> Term V (Arr τ1 τ2) -> Term V τ1 -> Term V τ2
     Abs : {τ1 τ2 : Type} -> (V τ1 -> Term V τ2) -> Term V (Arr τ1 τ2)

  eval : forall {τ} -> Term ⟦_⟧ τ -> ⟦ τ ⟧
  eval Tru = true
  eval Fals = false
  eval (Var v) = v
  eval (App y y') = eval y (eval y')
  eval (Abs y) = \t -> eval (y t)

  -- Closure conversion (a.k.a. lambda-lifting)

  

  
  -- you've seen it coming: the CPS transform!
  data Type! : Set where
    Boo! : Type!
    Not : Type! -> Type!
    _×_ : Type! -> Type! -> Type!



  cpsType : Type -> Type!
  cpsType Boo = Boo!
  cpsType (Arr τ1 τ2) = Not (cpsType τ1 × (Not (cpsType τ2)))

  -- lots of details are hidden in the paper, and Coq syntax is really not helping.
  -- it would help to study CPS separately I guess ;)
  mutual
    data Primop (V : Type! -> Set) (ρ : Type!) : (τ : Type!) -> Set where 
      Tru! : Primop V ρ Boo!
      Fals! : Primop V ρ Boo!
      Var! : {τ : Type! } -> (v : V τ) -> Primop V ρ τ
      Abs! : {τ1 : Type! } -> (V τ1 -> Term! V ρ) -> Primop V ρ (Not τ1)
      _,_ : {τ1 τ2 : Type! } -> V τ1 -> V τ2 -> Primop V ρ (τ1 × τ2)    
      π1 : {τ1 τ2 : Type! } -> V (τ1 × τ2) -> Primop V ρ τ1
      π2 : {τ1 τ2 : Type! } -> V (τ1 × τ2) -> Primop V ρ τ2
  

    data Term! (V : Type! -> Set) : (ρ : Type!) -> Set where 
      Halt! : {τ : Type! } -> (v : V τ) -> Term! V τ -- this is dependent here! (but not in Coq ??!)
      App!  : {ρ τ1 : Type! } -> V (Not τ1) -> V τ1 -> Term! V ρ
      Let   : {ρ τ1 : Type! } -> Primop V ρ τ1 -> (V τ1 -> Term! V ρ) -> Term! V ρ

  mutual 
    splice : {V : Type! -> Set} {τ1 τ2 : Type! } 
             (e1 : Term! V τ1) 
             (e2 : V τ1 -> Term! V τ2) -> Term! V τ2
    splice (Halt! v) e2 = e2 v
    splice (App! f x) e2 = App! f x
    splice (Let p e') e2 = Let (splicePrim p e2) (\x -> splice (e' x) e2)

    splicePrim : forall {t} {V : Type! -> Set} {τ1 τ2 : Type! } (p : Primop V τ1 t) (e2 : V τ1 -> Term! V τ2) -> Primop V τ2 t
    splicePrim Tru! e2 = Tru!
    splicePrim Fals! e2 = Fals!
    splicePrim (Var! v) e2 = Var! v
    splicePrim (Abs! e) e2 = Abs! (\x -> splice (e x) e2)
    splicePrim (y , y') e2 = y , y'
    splicePrim (π1 y) e2 = π1 y
    splicePrim (π2 y) e2 = π2 y


  cps : {τ : Type} -> {V : Type! -> Set} -> Term (V ∘ cpsType) τ -> Term! V (cpsType τ)
  cps Tru = Let Tru! Halt!
  cps Fals = Let Fals! Halt!
  cps (Var v) = Halt! v
  cps (App e1 e2) = splice (cps e1) (\f -> 
                    splice (cps e2) (\x ->
                    Let (Abs! Halt!) (\k -> 
                    Let (x , k) (\p -> 
                    App! f p))))
  cps (Abs e') = Let (Abs! (\p -> 
                            Let (π1 p) (\x -> 
                            Let (π2 p) (\k ->
                            splice (cps (e' x)) (\r -> 
                            App! k r)))))
                 Halt!


  
  inferTyp : forall {V} -> (τ : Type) -> UntypedLambdaCalculus.Term (V τ) -> Σ Type (Term V)
  inferTyp τ (UntypedLambdaCalculus.Var v) = τ , Var v
  inferTyp τ (UntypedLambdaCalculus.App y y') = {! !} , (App {! !} {! !})
  inferTyp τ (UntypedLambdaCalculus.Abs y) = {! !}
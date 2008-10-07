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

module HOAS where

  data Term : Set where
    App : Term -> Term -> Term
    -- Abs : (Term -> Term) -> Term -- ouch, posititity.



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


  -- Claim: We'll ensure that we don't store data in variables by always parameterizing on V.
  -- ie. instantiation does not incurr loss in generality.

  -- UsedTerm = {V : Set} -> Term V

  -- count variable uses
  numVars : Term ⊤ -> ℕ
  numVars (Var _) = 1
  numVars (App e1 e2) = numVars e1 + numVars e2
  numVars (Abs e') = numVars (e' tt)

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

  -- there is actually a mistake in the paper probably;
  -- they forget treat the top-level abstraction.

  -- The dreaded substitution with name capture...
  subst : {V : Set} -> Term (Term V) ->  Term V
  subst (Var e) = e
  subst (App e1 e2) = App (subst e1) (subst e2)
  subst (Abs e') = Abs (\x -> subst (e' (Var x))) 
  -- turns out very easy.
  -- (cleverness: nest terms!)

  

module SimplyTypedLambdaCalculus where

  data Type : Set where 
     Boo : Type
     Arr : Type -> Type -> Type


  -- Terms, with additional Type index.
  data Term (V : Type -> Set) : (τ : Type) -> Set where 
     Tru : Term V Boo
     Fals : Term V Boo
     Var : {τ : Type} -> (v : V τ) -> Term V τ
     App : {τ1 τ2 : Type} -> Term V (Arr τ1 τ2) -> Term V τ1 -> Term V τ2
     Abs : {τ1 τ2 : Type} -> (V τ1 -> Term V τ2) -> Term V (Arr τ1 τ2)

  
  -- you've seen it coming: the CPS transform!
  data Type! : Set where
    Boo! : Type!
    Not : Type! -> Type!
    _×_ : Type! -> Type! -> Type!



  cpsType : Type -> Type!
  cpsType Boo = Boo!
  cpsType (Arr τ1 τ2) = Not (cpsType τ1 × (Not (cpsType τ2)))


  mutual
    data Primop (V : Type! -> Set) : (τ : Type!) -> Set where 
      Tru! : Primop V Boo!
      Fals! : Primop V Boo!
      Var! : {τ : Type!} -> (v : V τ) -> Primop V τ
      Abs! : {τ1 τ2 : Type!} -> (V τ1 -> Term! V) -> Primop V (Not τ1)
      _,_ : {τ1 τ2 : Type!} -> Primop V τ1 -> Primop V τ2 -> Primop V (τ1 × τ2)    
      π1 : {τ1 τ2 : Type!} -> Primop V (τ1 × τ2) -> Primop V τ1
      π2 : {τ1 τ2 : Type!} -> Primop V (τ1 × τ2) -> Primop V τ2
  

    data Term! (V : Type! -> Set) : Set where 
      Halt! : {τ : Type!} -> (v : V τ) -> Term! V
      App!  : {τ1 : Type!} -> V (Not τ1) -> V τ1 -> Term! V
      Let   : {τ1 τ2 : Type!} -> Primop V τ1 -> (V τ1 -> Term! V) -> Term! V

  cps : {τ : Type} -> {V : Type! -> Set} -> Term (V ∘ cpsType) τ -> Term! V -- (cpsType τ)
  cps = ?
  

--   Inductive pterm : Type :=
--   | PHalt :
--     var result
--     -> pterm
--   | PApp : forall t,
--     var (t --->)
--     -> var t
--     -> pterm
--   | PBind : forall t,
--     pprimop t
--     -> (var t -> pterm)
--     -> pterm

--   with pprimop : ptype -> Type :=
--   | PVar : forall t,
--     var t
--     -> pprimop t
--     
--   | PTrue : pprimop Bool
--   | PFalse : pprimop Bool
--     
--   | PAbs : forall t,
--     (var t -> pterm)
--     -> pprimop (t --->)
-- 
--   | PPair : forall t1 t2,
--     var t1
--     -> var t2
--     -> pprimop (t1 ** t2)
--   | PFst : forall t1 t2,
--     var (t1 ** t2)
--     -> pprimop t1
--   | PSnd : forall t1 t2,
--     var (t1 ** t2)
--     -> pprimop t2.
  
  
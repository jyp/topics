module Polish where

open import Data.Nat
open import Data.List hiding (zip)

data List1 (T : Set1) : Set1 where
  Nil : List1 T
  Cons : (A : T) -> List1 T -> List1 T

-- Lists of Sets
SetList : Set1
SetList = List1 Set

-- Heterogeneous lists, indexed by the types of values in it.
data HList : SetList -> Set1 where
  Nil0 : HList Nil
  Cons0 : {A : Set} {Ts : SetList} -> (a : A) -> HList Ts -> HList (Cons A Ts)

-- Arbitary expressions in Polish notation.
-- Polish is indexed by the types in the stack produced by the expression.
data Polish : SetList -> Set1 where
  Val : {A : Set} {Rest : SetList} -> A -> Polish Rest -> Polish (Cons A Rest)
  App : {A B : Set} {Rest : SetList} -> Polish (Cons (A -> B) (Cons A Rest)) -> Polish (Cons B Rest)
  Stop : Polish Nil 

-- Evaluate the output of an expression
evalP : (Ts : SetList) -> Polish Ts -> HList Ts
evalP Nil Stop = Nil0
evalP (Cons A Ts) (Val a rest) = Cons0 a (evalP Ts rest)
evalP (Cons B Ts) (App p) with evalP _ p 
...                         | Cons0 f (Cons0 a rest) = Cons0 (f a) rest

-- Arbitrary expressions in Reverse Polish notation.
-- This can also be seen as an automaton that transforms a stack.
-- RPolish is indexed by the types in the stack consumed by the automaton.
data RPolish : SetList -> Set1 where
  RVal : {A : Set} {Rest : SetList} -> A -> RPolish (Cons A Rest) -> RPolish Rest 
  RApp : {A B : Set} {Rest : SetList} -> RPolish (Cons B Rest) -> RPolish (Cons (A -> B) (Cons A Rest)) 
  RStop : {Rest : SetList} -> RPolish Rest


-- Compute the final stack produced by an RPolish automaton.
produced : {input : SetList} -> RPolish input -> SetList
produced {input} RStop = input
produced (RApp {A} {B} {Rest} r) = produced {Cons B Rest} r
produced (RVal {A} {Rest} _ r) = produced {Cons A Rest} r

-- Evaluate the output of an RP automaton, given an input stack
evalRP : {Ts : SetList} -> (rp : RPolish Ts) -> HList Ts -> HList (produced rp)
evalRP RStop acc = acc 
evalRP (RVal v r) acc = evalRP r (Cons0 v acc)
evalRP (RApp r) (Cons0 f (Cons0 a acc)) = evalRP r (Cons0 (f a) acc)

-- Evaluate "as much as possible" of an RP automaton, /without knowing its input stack/
simplify : {Ts : SetList} -> RPolish Ts -> RPolish Ts
simplify (RVal a (RVal f (RApp r))) = simplify (RVal (f a) r)
simplify r = r

-- Gluing a Polish expression and an RP automaton.
-- This can also be seen as a zipper of Polish expressions.
-- Zip is indexed by the types produced in the final stack.
data Zip : SetList -> Set1 where
   zip : {Stack : SetList} -> (rp : RPolish Stack) -> Polish Stack -> Zip (produced rp)
   -- note that the Stack produced by the Polish expression matches
   -- the stack consumed by the automaton.

-- Move the zipper to the right, if possible.  The type gives evidence
-- that this function does not change the (type of) output produced.
right : {Stack : SetList} -> Zip Stack -> Zip Stack
right (zip l Stop) = (zip l Stop)
right (zip l (Val a r)) = zip (RVal a l) r
right (zip l (App r)) = zip (RApp l) r

-- Move the zipper to the left if possible. The type gives evidence
-- that this function does not change the (type of) output produced.
left : {Stack : SetList} -> Zip Stack -> Zip Stack
left (zip RStop r) = (zip RStop r)
left (zip (RVal a l) r) = zip l (Val a r)
left (zip (RApp l) r) = zip l (App r)

-- Evaluate the output of a whole Zip
evalZ : (Stack : SetList) -> Zip Stack -> HList Stack
evalZ .(produced rp) (zip {intermediateStack} rp p) = evalRP rp (evalP intermediateStack p)

        

infixr 0 _$_

_$_ : {A B : Set1} -> (A -> B) -> A -> B
f $ x = f x

test1 = {! (eval _ (App $ App $ Val _∷_ $ Val 1 $ App $ App $ Val _∷_ $ Val 2 $ Val [] $ Stop)) !}

test0 : {R : SetList} -> RPolish R
test0 = RVal 1 $ RVal 2 $ RVal _+_ $ RApp $ RApp $ RStop

--------------------------------------------------
-- Follows obsolete stuff.

data Couple12 (A : Set) (B : Set1) : Set1 where
  _,_ : A -> B -> Couple12 A B

fst : {A : Set} {B : Set1} -> Couple12 A B -> A
fst (a , b) = a


snd : {A : Set} {B : Set1} -> Couple12 A B -> B
snd (a , b) = b


eval0 : {A : Set} {Rest : SetList} -> Polish (Cons A Rest) -> Couple12 A (Polish Rest)
eval0 (Val a rest) = a , rest
eval0 (App p) = let 
   fp' = eval0 p
   ap'' = eval0 (snd fp')
  in fst fp' (fst ap'') , snd ap''



{-# LANGUAGE MultiParamTypeClasses, GADTs #-}

import Data.Char
import Data.List
import Data.Maybe
import Data.FingerTree
import Data.Monoid
-- import Data.Sequence

-- Eventually one should convert this type to a grammar.
-- (See UU tricks to do this)
data P s where
     Sym :: (s -> Bool) -> P s 
     (:*:) :: P s -> P s -> P s
     (:|:) :: P s -> P s -> P s
     (:>) :: String -> P sc


----------------------------


-- An element of the parse tree can be either a symbol or a non-terminal
data El = S Char | Nt Int [El]
    deriving (Show,Eq)

-- Predicates over elements
type Check = El -> Bool

-- A production rule. The non-terminal is the 1st argument.
data Rule = Rule Int [Check] 

-- A grammar is a set of rule.
type Grammar = [Rule]

-- A proto-phrase: an unstructured list of elements.
type Seq = [El]

-- The state is a collection of all possible proto-phrases.
type State = [Seq]

-- Match a proto-phrase against the rhs of a production rule
match :: [Check] -> [El] -> Bool
match [] _ = True
match (x:xs) (y:ys) = x y && match xs ys
match _ _ = False

-- Try to apply a rule to a proto-phrase. 
apply :: Rule -> Seq -> Maybe Seq
apply (Rule n xs) ys = listToMaybe [prefix ++ [Nt n matched] ++ suffix |
                                    (prefix,rest) <- zip (inits ys) (tails ys), 
                                    match xs rest, let (matched,suffix) = splitAt (length xs) rest]
        
-- Apply all rues to a proto-phrase
applyAll :: Grammar -> Seq -> Seq
applyAll g s = foldr (\rule -> tillConverge (apply rule)) s g

tillConverge :: (a -> Maybe a) -> (a -> a)
tillConverge f a = case f a of
    Nothing -> a
    Just x -> tillConverge f x

-- Merge (sequence) two sets of proto-phrases
merge :: Grammar -> State -> State -> State
merge g ls rs = nub [applyAll g (l ++ r) | l <- ls, r <- rs]

-- Wrap it up as a monoid...
newtype M = M State deriving Show

instance Measured M Char where
    measure c = M [[S c]]

instance Monoid M where
    mappend (M s) (M t) = M (merge grammar s t)
    mempty = M [[]]

------------------------------
-- Helper functions to write rules.
sym c (S c') = c == c'
sym _ _ = False

symbol f (S c) = f c
symbol _ _ = False

nt x (Nt y _) = x == y
nt _ _ = False


-- Test grammar.
grammar = [Rule 1 [sym '(', nt 1, sym ')'],
           Rule 1 [nt 1, sym '+', nt 1],
           Rule 1 [symbol isDigit]
          ]



test = measure $ fromList $ "1+((2+4)+(5+4))" ++ concat (replicate 1000 "+1+((2+4)+(5+4))")




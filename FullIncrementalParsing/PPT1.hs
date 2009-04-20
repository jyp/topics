{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, UndecidableInstances, TypeOperators #-}

import Data.Char
import Data.List
import Data.Maybe
import Data.FingerTree
import Data.Monoid
import Control.Applicative hiding (empty)
import qualified Control.Applicative as A (empty)

-- import Data.Sequence

-- data P s where
--      Sym :: (s -> Bool) -> P s 
--      (:*:) :: P s -> P s -> P s
--      (:|:) :: P s -> P s -> P s
--      (:>) :: String -> P s



----------------------------



type Check el = el -> Bool

data Rule el = Rule ([el] -> el) [Check el]

type Seq el = [el]

type Grammar el = [Rule el]

type State el = [Seq el]

match :: [Check el] -> [el] -> Bool
match [] _ = True
match (x:xs) (y:ys) = x y && match xs ys
match _ _ = False


apply :: Rule el -> Seq el -> Maybe (Seq el)
apply (Rule f xs) ys = listToMaybe [prefix ++ [f matched] ++ suffix |
                                    (prefix,rest) <- zip (inits ys) (tails ys), 
                                    match xs rest, let (matched,suffix) = splitAt (length xs) rest]

applyAny :: Grammar el -> Seq el -> Maybe (Seq el)
applyAny g s = (foldr (<|>) Nothing) [apply r s | r <- g]

applyAll :: Grammar el -> Seq el -> Seq el
applyAll g = tillConverge (applyAny g)

newtype (f :.: g) a = O (f (g a))

instance (Functor f, Functor g) => Functor (f :.: g) where
    fmap f (O v) = O $ fmap (fmap f) $ v

instance Applicative g => Applicative ((->) b :.: g) where
    pure = O . const . pure
    O f <*> O x = O $ \b -> f b <*> x b

instance Alternative f => Alternative (((->) b) :.: f) where
    empty = O $ \b -> A.empty
    O f <|> O g = O $ \a -> f a <|> g a

tillConverge :: (a -> Maybe a) -> (a -> a)
tillConverge f a = case f a of
    Nothing -> a
    Just x -> tillConverge f x

merge :: Tree el => Grammar el -> State el -> State el -> State el
-- TODO: in fact nub should just be comparing the top-level kind of non-terminal
merge g ls rs = nub [applyAll g (l ++ r) | l <- ls, r <- rs]


class Eq el => Tree el where
    getGrammar :: Grammar el

newtype M el = M (State el) deriving Show


instance Tree el => Monoid (M el) where
    mappend (M s) (M t) = M (merge getGrammar s t)
    mempty = M [[]]


------------------------------



data Expr = C Char | Add Expr Expr | Paren Expr | I Int
    deriving (Show, Eq)

sym c = symbol (== c)

symbol f (C c) = f c
symbol _ _ = False

proper (C _) = False
proper _ = True

instance Tree Expr where
    getGrammar = [Rule (\[_,m,_] -> Paren m) [sym '(', proper, sym ')'],
                  Rule (\[l,_,r] -> Add l r) [proper, sym '+', proper],
                  Rule (\[C d] -> I (ord d - ord '0')) [symbol isDigit]
                 ]

instance Measured (M Expr) Char where
    measure c = M [[C c]]

t :: FingerTree (M Expr) Char
t = fromList $ "1+((2+4)+(5+4))" -- ++ concat (replicate 1000 "+1+((2+4)+(5+4))")

test = measure $ t 


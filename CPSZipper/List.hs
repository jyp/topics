{-# LANGUAGE GADTs, RankNTypes #-}

data Tree a where
    Cat :: Tree a -> Tree a -> Tree a
    Unit :: a -> Tree a

append []     ys = ys
append (x:xs) ys = x : append xs ys


toList :: Tree a -> [a]
toList (Unit a) = a : []
toList (Cat l r) = toList l ++ toList r

(+++) :: (([a] -> [a]) -> [a]) -> (([a] -> [a]) -> [a]) -> [a]
f +++ g = undefined


appendCBNCPS :: [t] -> [t] -> (forall b. ([t] -> b) -> b)
appendCBNCPS [] ys k = k ys
appendCBNCPS (x:xs) ys k = k (appendCBNCPS xs ys) (x :)

toListCBNCPS :: Tree a -> ([a] -> [a]) -> [a]
toListCBNCPS (Unit a) k = k [a]
toListCBNCPS (Cat l r) k = k ((+++) (toListCBNCPS l) (toListCBNCPS r))

toListCBNCPS' t = toListCBNCPS t id





toListCBVCPS :: Tree a -> ([a] -> b) -> b
toListCBVCPS (Unit a) k = k [a]
toListCBVCPS (Cat l r) k = 
   toListCBVCPS l $ \x1 ->
   toListCBVCPS r $ \x2 ->
   -- k (x1 ++ x2) 
   appendCBVCPS x1 x2 k
   

toListCBVCPS' t  = toListCBVCPS t id



appendCBVCPS :: [t] -> [t] -> (forall b. ([t] -> b) -> b)
appendCBVCPS []     ys k = k ys
appendCBVCPS (x:xs) ys k = appendCBVCPS xs ys $ \zs -> k (x : zs)


-- let b = [a]

type K a = [a] -> [a]

data Lam a = Id | Lam1 (Lam a) (Tree a) | Lam2 (Lam a) [a]
    
toListCBVCPSDefun :: Tree a -> Lam a -> [a]
toListCBVCPSDefun (Unit a) k = apply k [a]
toListCBVCPSDefun (Cat l r) k = toListCBVCPSDefun l (Lam1 k r)

apply :: Lam a -> [a] -> [a]
apply (Lam1 k r)  x1 = toListCBVCPSDefun r (Lam2 k x1)
apply (Lam2 k x1) x2 = apply k (x1 ++ x2)
apply Id x1 = x1
    
toListCBVCPSDefun' t = toListCBVCPSDefun t Id




realToList :: Tree a -> ([a] -> [a])
realToList (Cat l r) = \k -> realToList l (realToList r k)
realToList (Unit a) = \k -> a : k

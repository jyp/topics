{-# LANGUAGE GADTs #-}
list = [1..5]

--------
-- Direct

mapD f [] = []
mapD f (x:xs) = f x : mapD f xs

testD = mapD succ list

-------- 
-- CPS0

succC n k = k (n + 1)

mapC f [] k = k []
mapC f (x:xs) k = 
  (f x) $ \a ->
  (mapC f xs) $ \b ->
  k (a : b)

testC = mapC succC list

-------- 
-- CPS1

mapC1 f [] k = k []
mapC1 f (x:xs) k = 
  (mapC1 f xs) $ \b ->
  k (f x : b)

testC1 = mapC1 succ list

--------------
-- CPS2: put arguments in better order

mapC2 :: (t -> a) -> ([a] -> b) -> [t] -> b
mapC2 = \f -> \k -> \l -> case l of
    [] -> k []
    (x:xs) -> mapC2 f (\b -> k (f x : b)) xs

testC2 = mapC2 succ id list




---------------
-- Defun CPS2

rec :: ([a] -> t) -> [a] -> t
rec k [] = k []
rec k (x:xs) = rec (\b -> k (x : b)) xs


{-
data LamF1 a t where
    LamF1 :: ([a] -> t) -> a -> LamF1 a t -- (\b -> k (x : b))

aux :: LamF1 a t -> [a] -> t
aux (LamF1 k x) b = k (x : b)

mp k [] = k []
mp k (x:xs) = mp (aux (LamF1 k x)) xs

-}

-- but!!!!
rec' :: ([a] -> [a]) -> ([a] -> [a])
rec' k [] = k []
rec' k (x:xs) = rec' (\b -> k (x : b)) xs

mp' = rec' id

data ListFun a where -- defunctionalized list functions
    Id :: ListFun a
    CompCons :: ListFun a -> a -> ListFun a

appFun :: ListFun a -> [a] -> [a]
appFun (CompCons k x) b = appFun k (x : b) -- (\b -> k (x : b))
appFun (Id) b = b

mp :: ListFun a -> [a] -> [a]
mp k [] = appFun k []
mp k (x:xs) = mp (CompCons k x) xs


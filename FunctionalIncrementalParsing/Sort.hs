{-# OPTIONS -i../Machines #-}
import SuspensionVM 
import Control.Applicative

insert y [] = [y]
insert y (x:xs) = if x < y then x : insert y xs else y : x : xs

sort (x:xs) = insert x (sort xs)
sort [] = []

-- Unfortunately evalL will not do any computation :
-- profile $ evalL $ pushSyms "jcsdjqwioheof" $ toProc sort' == "$.$.$.$.$.$.$.$.$.$.$.$.$.?"
sort' :: P Char [Char]
sort' = case_ (pure []) $
  \x -> insert x <$> sort'




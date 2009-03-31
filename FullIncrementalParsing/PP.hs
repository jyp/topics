import Data.List
import Data.Maybe
-- import Data.Sequence

-- data P s a where
--     Sym :: (s -> Bool) -> P s 
--     (:*:) :: P s -> P s -> P s
--     (:|:) :: P s -> P s -> P s
--     (:>) :: String -> P s a


type Check = El -> Bool
data El = S Char | Nt Int [El]
    deriving Eq

data Rule = Rule Int [Check] 

type Seq = [El]

type Grammar = [Rule]

type State = [Seq]

match :: [Check] -> [El] -> Bool
match [] _ = True
match (x:xs) (y:ys) = x y && match xs ys
match _ _ = False


apply :: Rule -> [El] -> Maybe [El]
apply (Rule n xs) ys = listToMaybe [prefix ++ [Nt n matched] ++ suffix |
                                    (prefix,rest) <- zip (inits ys) (tails ys), 
                                    match xs rest, let (matched,suffix) = splitAt (length xs) rest]
        
apply' :: Rule -> Seq -> Seq
apply' rule ys = maybe ys id (apply rule ys)  

applyAll :: Grammar -> Seq -> Seq
applyAll g s = foldr apply' s g

merge :: Grammar -> State -> State -> State
merge g ls rs = nub [applyAll g (l ++ r) | l <- ls, r <- ls]



------------------------------



import qualified Data.Set as S
import Test.QuickCheck
import Data.Function
import Data.List
type Set = S.Set

type Oblivous a = ((a,a) -> (a,a)) -> [a] -> [a]

bubble :: Oblivous a
bubble xchg list = iterate pass list !! length list
    where pass [] = []
          pass [x] = [x]
          pass (x:y:ys) = a:pass (b:ys) where (a,b) = xchg (x,y)



data I = Min I I | Max I I | Ix Int
    deriving Show

initial (x,y) = (Min x y, Max x y)

testI f n = f initial (fmap Ix [1..n])


-- Using this we can test a given length in polynomial time. 
-- (Because mix/max are polynomial, and because a sort normally has polynomial number of swaps)

-- We therefore achieve better than 2^n already!
type MinMax = [Set Int]


mmin a b = simpl (a ++ b)

mmax :: MinMax -> MinMax -> MinMax
mmax a b = simpl [x `S.union` y | x <- a, y <- b ]

simpl' [] = []
simpl' (s:ss) = s : simpl' (filter (not . (s `S.isSubsetOf`)) ss)

simpl = simpl' . sortBy (compare `on` S.size)


testQ f n = f (\(x,y) -> (mmin x y, mmax x y)) (fmap ix [1..n])
    where ix a = [S.singleton a]
          ix :: Int -> MinMax


propDistr a b c d = max (min a b)  (min c d) == minimum [max a c, max b c, max a d, max b d]
propSimpl x as bs = min (maximum (x:as)) (maximum (x : as ++ bs)) == maximum (x:as)



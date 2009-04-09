import Control.Exception (assert)

import Data.Array

type Matrix a = Array (Int,Int) a 
type Vector a = Array Int a
type Graph = Matrix Bool

constV n x = listArray (1,n) (repeat x)

mul :: Num a => Matrix a -> Vector a -> Vector a
mul m v = array (1,b) [(j,sum [m!(i,j) * v!i | i <- [1..a]]) | j <- [1..b]]
    where ((1,1),(a,b)) = bounds m
          (1,a') = bounds v
          p = assert (a == a') "dimensions must match"

simul :: (Num a) => Matrix a -> Vector a -> [Vector a]
simul m = iterate (mul m)

degree :: Graph -> Int -> Int
degree g i = length [() | j <- [1..b], g!(i,j) ]
    where ((1,1),(_,b)) = bounds g

metropolis :: (Fractional p, Ord p) => Graph -> Vector p -> Matrix p
metropolis g pi = listArray bnds $ map p (range bnds)
    where p (i,j) | i /= j = if g!(i,j) then min 1 ((pi!j * d i)/(pi!i * d j) ) / d i 
                                       else 0
                  | i == j = 1 - sum [p (i,l) | l <- [1..b], l /= i]
          d = fromIntegral . degree g
          bnds@((1,1),(_,b)) = bounds g
          



 --                 r   l   u   r'  w
test = {- r -} [[   1,  1,  0,  0,  0]
       {- l -} ,[   0,  0,  1,  1,  1]
       {- u -} ,[   1,  1,  0,  0,  0]
       {- r'-} ,[   0,  0,  1,  1,  1]
       {- w -} ,[   0,  0,  1,  1,  1]
               ]

testG = listArray bnds [ind(test?i?j) | (i,j) <- range bnds ]
    where bnds = ((1,1),(5,5)) 
          (x:_)  ? 1 = x
          (_:xs) ? n = xs ? (n-1)
          ind 0 = False
          ind 1 = True

-- resP = metropolis testG (constV 5 (1 / 5))
resP = metropolis testG (listArray (1,5) $ norm [1,1,1,1,10])
          

norm l = map (/ sum l) l

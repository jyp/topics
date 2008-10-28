{-# LANGUAGE ExistentialQuantification, RankNTypes #-}

data Expr = ConstE Int | AddE Expr Expr | NegE Expr

data Code = Push Int | Add | Neg | Seq Code Code

comp :: Expr -> Code
comp (ConstE n) = Push n
comp (NegE e) = Seq (comp e) Neg
comp (AddE e1 e2) = Seq (comp e1) (Seq (comp e2) Add)

intStack :: Code -> Int
intStack i = head (int' i [])
    where 
        int' (Push n) s = n :s 
        int' Neg (n:s) = (negate n) : s
        int' Add (n : m : s) = (m + n) : s
        int' (Seq i1 i2) s = int' i2 (int' i1 s)

intExp e = intStack (comp e)

example = AddE (ConstE 5) (ConstE 3)

test = intExp example


-- CBN CPS

data Code' = Push' Int | Add' | Neg' 
    | Seq' (forall a. (Code' -> a) -> a) (forall a. (Code' -> a) -> a)

comp' :: forall a. Expr -> (Code' -> a) -> a
comp' (ConstE n)   k = k (Push' n)
comp' (NegE e)     k = k (Seq' (comp' e)  (\k -> k Neg'))
comp' (AddE e1 e2) k = k (Seq' (comp' e1) (\k -> k (Seq' (comp' e2) (\k -> k Add'))))

intStack' :: (forall a. (Code' -> a) -> a) -> Int
intStack' i = head (int' i [])
    where 
        int' :: (forall a. (Code' -> a) -> a) -> [Int] -> [Int]
        int' i s = i $ \v -> case (v,s) of
            (Push' n   , s           ) -> n :s 
            (Neg'      , (n:s)       ) -> (negate n) : s
            (Add'      , (n : m : s) ) -> (m + n) : s
            ((Seq' i1 i2), s         ) -> int' i2 (int' i1 s)


intExp' e = intStack' (comp' e)

-- example = AddE (ConstE 5) (ConstE 3)
-- 
-- test = intExp example




data Tree a  = Node a (Tree a) (Tree a)
             | Leaf
    deriving (Show)

toTree d [] = Leaf
toTree d (x:xs) = Node x l (toTree (d+1) xs')
    where (l,xs') = toFullTree d xs

toFullTree 0 xs = (Leaf, xs)
toFullTree d [] = (Leaf, [])
toFullTree d (x:xs) = (Node x l r, xs'')
    where (l,xs' ) = toFullTree (d-1) xs
          (r,xs'') = toFullTree (d-1) xs'

Node 1 (Node 2 Leaf Leaf) 
       (Node 3 (Node 4 (Node 5 Leaf Leaf) 
                       (Node 6 Leaf Leaf)) 
               (Node 7 (Node 8 (Node 9 (Node 10 Leaf Leaf) 
                                       Leaf) 
                                Leaf)
                        Leaf))

Node 1 (Node 2 Leaf Leaf) 
       (Node 3 (Node 4 (Node 5 Leaf Leaf) 
                       (Node 6 Leaf Leaf)) 
               (Node 7 (Node 8 (Node 9 (Node 10 Leaf Leaf) 
                                       (Node 11 Leaf Leaf))
                               (Node 12 (Node 13 Leaf Leaf) 
                                        (Node 14 Leaf Leaf)))
                       (Node 15 (Node 16 (Node 17 (Node 18 (Node 19 Leaf Leaf) 
                                                           (Node 20 Leaf Leaf)) 
                                                  (Node 21 (Node 22 Leaf Leaf) 
                                                           (Node 23 Leaf Leaf)))
                                         (Node 24 (Node 25 (Node 26 Leaf Leaf) 
                                                           (Node 27 Leaf Leaf))
                                         (Node 28 (Node 29 Leaf Leaf) 
                                                  (Node 30 Leaf Leaf)))) 
                                (Node 31 (Node 32 (Node 33 (Node 34 (Node 35 (Node 36 Leaf Leaf) 
                                                                             (Node 37 Leaf Leaf)) 
                                                                    (Node 38 (Node 39 Leaf Leaf)
                                                                             (Node 40 Leaf Leaf))) 
                                                           (Node 41 (Node 42 (Node 43 Leaf Leaf) 
                                                                             (Node 44 Leaf Leaf)) 
                                                                    (Node 45 (Node 46 Leaf Leaf) 
                                                                             (Node 47 Leaf Leaf)))) 
                                                  (Node 48 (Node 49 (Node 50 Leaf Leaf) Leaf) Leaf)) Leaf))))

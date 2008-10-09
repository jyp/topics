

Requirements on the data type:

* indexed data type

    _[_] :: T a -> Int -> a

* _can_ be constructed as such:

    fromList :: [a] -> T a
  
* $t[i]$ in $O(\log i)$

  This is the most important property.x
  Note that access does not depend on the size of the tree!
  In particular the above still holds if bottoms are present
  in the non-accessed part of the tree.

* $fromList (l ++ \bottom) [i]$ will work for all $i < |l|$


Disentangling the construction from the parsing can be done by
CPS-transforming the direct construction algorithm. 

we obtain the following functions:

    initial :: Partial a
    continue :: [a] -> Partial a -> Partial a
    finish :: Partial a -> T a

where partial result is represented as

    type Partial a = [a] -> T a


Given this, we can express the incremental performance as follows:

    p1 := continue l1 initial
    f1 := spine (finish p1)  -- O (|l1|), where spine evaluates the spine.
    p2 := continue l2 p1
    f2 := spine (finish p2)  -- O (|l2| + log |l1|)


We could also assign amortized costs as such:

   
function       cost
------------   --------------------
initial        O(1)
continue l p   O(length l)
finish p       O(log (length p))
f[i]           O(log i)

However, this is not really descriptive of what we want, because
we want to make explicit that we don't pay the cost for "continue"
until we actually access the corresponding elements.


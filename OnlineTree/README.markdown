references:
http://hackage.haskell.org/cgi-bin/hackage-scripts/package/lazyarray
http://citeseer.ist.psu.edu/95126.html


     class EfficientLazy t p where
       index :: Int -> t a -> a
       initial :: t a
       continue :: Int -> [a] -> t a -> t a

     toTree l = continue 0 l $ initial


let ev(n,t) indicate that the spine of the tree is evaluated up element n.


ev(i,t) => index i t is O(log i)
ev(i0,t), i0 < i1 => index i1 t is O(max (log i1) (t1-t0)) and ev(i1,t)

We have choices for continue: we can make it strict or lazy in the tree.

strict:
ev(i0,t), i0 < i1 => continue i1 t l is O(max (log i1) (t1-t0)) and ev(i1,t) 

lazy:
ev(i0,t), i0 < i1 => continue i1 t l is O(log i1) (amortized) and ev(i0) 


----------------------------
OLD STUFF


Requirements on the data type:

* indexed data type

    index :: Int -> T a -> a

* _can_ be constructed as such:

    fromList :: [a] -> T a
  
* $index i t$ in $O(\log i)$

  This is the most important property.
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


# Applications

- Reading a file on disk
- GUI for a PDF reader
- Incremental parsing :)
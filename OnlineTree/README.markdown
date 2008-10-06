

Requirements on the data type:

* indexed data type

    _[_] :: T a -> Int -> a

* _can_ be constructed as such:

    fromList :: [a] -> T a
  
* $t[i]$ in $O(\log i)$

  note that access does not depend on the size of the tree!
  In particular the above still holds if bottoms are present.

* $fromList (l ++ \bottom) [i]$ will work for all $i < |l|$


Disentangling the construction from the parsing is not easily done.

The above (fromList) is too restrictive: how can we express partially
constructed trees?

A partial result can be represented as

    type Partial a = [a] -> T a

with

    continue :: [a] -> Partial a -> Partial a
    finish :: Partial a -> T a

We could say that finish must cost only propotional to $log n$;
and continue is proportional to $length (1st arg)$ 

    

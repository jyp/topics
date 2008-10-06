

Requirements on the data type:

* indexed data type

    _[_] :: T a -> Int -> a

* disentangling the construction from the parsing is not easily done

    fromList :: [a] -> T a

  The above is too restrictive (unless the intermediate list is somehow
  deforested)

* $t[i]$ in $O(\log i)$

  note that access does not depend on the size of the tree!
  In particular the above still holds if bottoms are present.

* $fromList (l ++ \bottom) [i]$ will work for all $i < |l|$



  




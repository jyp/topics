From oleg-at-okmij.org Wed Apr 27 16:17:04 2005
To: haskell@haskell.org
Subject: Zipper as a delimited continuation
From: oleg-at-pobox.com
Message-ID: <20050427231704.DE8F9ABCC@Adric.metnet.navy.mil>
Date: Wed, 27 Apr 2005 16:17:04 -0700 (PDT)
Status: OR


This is the first part of a reply to a query about a zipper with two
foci, posted on this list by Oktaviandi Hadi Nugraha on Apr 13. In
this part we introduce the framework to answer the question.

Our treatment of zipper is quite different from that of Huet (JFP,
1997) and Hinze and Jeuring (JFP 2001). Our zipper is polymorphic over
the data structure to traverse, and the zipper creation procedure is
generic and does not depend on the data structure at all.  Different
data structures or different realizations of the same abstract data
structure can use the same zipper and the same zipper creation and
manipulation functions. Our zipper type depends only on the interface
(but not the implementation!) of a traversal function. Our zipper is a
derivative of a traversal function rather than that of a data
structure itself.

Zipper is a construction that lets us replace an item deep in a
complex data structure, e.g., a tree or a term, without any
mutation. The resulting data structure will share as much of its
components with the old structure as possible. The old data structure
is still available (which can be handy if we wish to 'undo' the
operation later on). Zipper is essentially an `updateable' and yet
pure functional cursor into a data structure.

Zipper is also a delimited continuation reified as a data
structure. In this message, we use delimited continuations directly to
derive the zipper. We will be relying on the delimited continuation
framework by R. Kent Dybvig, Simon Peyton-Jones and Amr Sabry. Their
framework supports shift/reset with multiple prompts and fully
polymorphic answertypes. We will be using a slightly modified version
of the framework, where the CC monad is a transformer rather than the
stand-alone monad.

> {-# OPTIONS -fglasgow-exts #-}
> module Zipper1 where
>
> -- Part of the Dybvig, Sabry, Peyton-Jones' library
> -- adjusted from being a monad to be a monad transformer
> import CC_2CPST
> import Control.Monad.Identity
> import Control.Monad.Trans

We will be using the familiar shift/reset control operators,
implemented as follows:

> promptP :: Monad m => (Prompt r a -> CC r m a) -> CC r m a
> promptP f = do p <- newPrompt; pushPrompt p (f p)
>
> shiftP :: Monad m => 
> 	  Prompt r b -> ((CC r m a -> CC r m b) -> CC r m b) -> CC r m a
> shiftP p f = letSubCont p $ \sk -> 
>                pushPrompt p (f (\c -> 
>                  pushPrompt p (pushSubCont sk c)))

We need multiple prompts in the second part to be posted later.


The derivation of the zipper starts with a term traversal function. The
zipper will be as good and powerful as the traversal function. Let us
adopt as a running example the familiar and dear data structure:

> data Term = Var String | A Term Term | L String Term 
>             deriving (Eq,Show)

In this message, we chose the following function to traverse the lambda-term:

> data Direction = Down | DownRight | Up | Next deriving (Eq, Show)
> traverse :: (Monad m)=> (Term -> m (Maybe Term, Direction)) -> Term -> m Term
> traverse tf term = do
> 		   (term', direction) <- tf term
> 		   let new_term = maybe term id term'
> 		   let select Up t = return t
> 		       select Next t@(Var _) = return t
> 		       select dir t@(L v t1) | dir == Next || dir == Down
> 			   = do
> 			     t1' <- traverse tf t1
> 			     return $ L v t1'
> 		       select DownRight t@(A t1 t2) =
> 			   do
> 			   t2' <- traverse tf t2
> 			   return $ A t1 t2'
> 		       select dir t@(A t1 t2) | dir == Next || dir == Down
> 			   = do
> 			     t1' <- traverse tf t1
> 			     t2' <- traverse tf t2
> 			     return $ A t1' t2'
> 		   select direction new_term

The function `traverse' receives the traversal function `tf' and the
lambda-term, and walks and _updates_ the term, as guided by `tf'.  The
traversal function receives the current subterm and should return a
pair. If the first component of a pair is (Just t'), then t' replaces
the current subterm. The second component of tf's result is the
direction to proceed. The direction Next means proceed in the
depth-first order. Other directions may be used to skip some parts of
the term and so avoid walking the whole term. The function is written
in a monadic style (for an arbitrary monad m). We shall need that
later.

We will be using the following term as a running example:

> -- P2 numeral
> term1 = L "f" (L "x" (A (A f (L "f" (A f (L "f" (L "x" x)))))
> 			  (A (A f (L "f" (L "x" x))) x)))
> 	 where [f,x] = map Var ["f","x"]

The first test simply traverses the whole term, makes no alterations
and returns the (copy of the) term:

> testt1 = runIdentity (traverse (\term -> return (Nothing,Next)) term1)

-- *Zipper0> testt1 == term1
-- True

To make sure that we really traverse the term, we can print out all
the encountered subterms:

> testt2 = traverse tf term1
>     where tf term = print term >> return (Nothing,Next)


We instantiate `traverse' for the IO monad this time. We can skip some
parts of the term during the traversal:

> testt3 = traverse tf term1
>     where 
>     tf term@(A (Var "f") _)  = do
> 			         print "cutting" >> print term
> 			         return (Nothing,Up)
>     tf term = print term >> return (Nothing,Next)

and we can modify the term

> testt4 = runIdentity (traverse tf term1)
>     where tf (L "x" (Var "x")) = return (Just (L "y" (Var "y")),Next)
> 	    tf _ = return (Nothing,Next)

which indeed returns term1 with all occurrences of (L "x" (Var "x"))
replaced with (L "y" (Var "y")).


Now we an introduce the zipper:

> data Zipper r m term dir = 
>     Zipper term (CC r m (Maybe term, dir) -> CC r m (Zipper r m term dir)) 
>   | ZipDone term

It is indeed polymorphic over the term to traverse (as well over the
source monad 'm'). We can use this Zipper, as it is, for _any_
data structure that can be traversed by a function that looks like
`traverse'.

Creating the zipper equally generic:

> zip'term :: (Monad (CC r m), Monad m) =>
> 	    ((term -> CC r m (Maybe term, dir)) -> term -> CC r m term)
> 	    -> term -> CC r m (Zipper r m term dir)
> zip'term trav term = promptP (\p -> trav (tf p) term >>= (return . ZipDone))
>     where tf p term = shiftP p (\k -> return (Zipper term k))

Both Zipper and its creation function depend neither on the
representation of the term nor on the traversal strategy.  All the
information about the data structure and its traversal is
encapsulated in one single function `trav'.

We can now examine term1, subterm by subterm, using the cursor,
zipper, rather than the enumerator, traverse:

> zip'through (ZipDone term) = liftIO (print "Done" >> print term)
> zip'through (Zipper term k) = do
> 			        liftIO $ print term
> 			        k (return (Nothing,Next)) >>= zip'through
> tz1 :: IO () = runCC (zip'term traverse term1 >>= zip'through)

In a sense, we have `inverted' the operation of term traversal. With
the cursor, we can keep arbitrary state from one traversal step to
another.

The cursor provided by zipper is updateable. We can now descend (or
walk) to the desired node, replace it, and zip up the result to yield
the updated term:

> zip'move dir (Zipper term k) = 
>     liftIO (print dir >> print term) >> k (return (Nothing,dir))

> zip'upr (Zipper term k) nt = do 
>        liftIO (print term >> print "replacing with" >> print nt)
>        k (return (Just nt,Up))
> zip'all'the'way'up (ZipDone term) = return term
> zip'all'the'way'up (Zipper term k) = 
>     k (return (Nothing,Up)) >>= zip'all'the'way'up
>
> tz2 :: IO () 
>     = runCC (
> 	 do
>	 z <- zip'term traverse term1
>	 z1 <- zip'move Next z
>	 z1 <- zip'move Next z1
>	 z2@(Zipper (A _ _) k) <- zip'move DownRight z1
>	 res <-  zip'upr z2 (A (Var "x") (Var "x")) >>= zip'all'the'way'up
>	 liftIO $ (print "Result" >> print res)
> 	 --zip'through z1
> 	 )

*Zipper0> tz2
Next
L "f" (L "x" (A (A (Var "f") (L "f" (A (Var "f") (L "f" (L "x" (Var "x"))))))
                (A (A (Var "f") (L "f" (L "x" (Var "x")))) (Var "x"))))
Next
L "x" (A (A (Var "f") (L "f" (A (Var "f") (L "f" (L "x" (Var "x"))))))
         (A (A (Var "f") (L "f" (L "x" (Var "x")))) (Var "x")))
DownRight
A (A (Var "f") (L "f" (A (Var "f") (L "f" (L "x" (Var "x"))))))
  (A (A (Var "f") (L "f" (L "x" (Var "x")))) (Var "x"))
A (A (Var "f") (L "f" (L "x" (Var "x")))) (Var "x")
"replacing with"
A (Var "x") (Var "x")
"Result"
L "f" (L "x" (A (A (Var "f") (L "f" (A (Var "f") (L "f" (L "x" (Var "x"))))))
                (A (Var "x") (Var "x"))))


We should point out that we are given an arbitrary number of cursors
over the same data structure: for example, in `tz2', the cursor 'z1'
is still valid at the end, and still points out to the `third'
subterm. The cursor 'z2' is valid as well. All these cursors are
isolated: the updates done with the cursor 'z2' and invisible to
the cursor 'z1' (as we can see if we uncomment the last statement in
tz2). Essentially, each cursor runs in its own transaction. In the
second part we will discuss how to make cursors that see the updates
of each other. Contrary to the traditional database wisdom, for zippers,
it is far harder to implement lower isolation modes than the higher
ones.


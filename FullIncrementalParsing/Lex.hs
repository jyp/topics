{-# LANGUAGE MultiParamTypeClasses #-}

import Data.Monoid
import Data.Array


-- Each symbol of the input can be converted into a transition function:
class Monoid o => Lexer i s o where
    transition :: i -> Trans s o

-- A transition transforms the state and yields some output.
type Trans s o = s -> (s,o)
    

-- We also assume a monoid on the output data. (It can be put in a tree, parsed by a monoidal parser, go through a 2nd stage of monoidal lexing, etc.)
(<>) :: Monoid o => o -> o -> o
(<>) = mappend

-- So the empty transition is
emptyTransition s = (s,mempty)

-- We can also assume a finite number of states.
class (Ix s, Bounded s) => Finite s where

series :: Finite s => [s]
series = range (minBound, maxBound)

-- Goal: make the lexer monoidal.
-- That is, we need a conversion function from transitions to a monoid structure.

-- Version 0: not useful, because the ouputs are not reusable/cached

{-

data Monotrans s o = Monotrans (s -> (s,o))

toMono = Monotrans 

instance (Monoid o, Finite s) => Monoid (Monotrans s o) where
    mappend (Monotrans f) (Monotrans g) = Monotrans (\s0 -> let (s1,o)  = f s0
                                                               (s2,o') = g s1
                                                            in (s2,o <> o'))
    mempty = Monotrans (\s -> (s,mempty))

-}

{-
---------------
-- V1
-- Here the outputs are precomputed/reusable, but the append operation is very slow!



data Monotrans s o = Monotrans [(s,o,s)]

toMono t = Monotrans [(s,o,s') | s <- series, let (s',o) = t s]

instance (Monoid o, Finite s) => Monoid (Monotrans s o) where
    mappend (Monotrans f) (Monotrans g) = Monotrans [(s0,o <> o',s2) | (s0,o,s1) <- f, (s1',o',s2) <- g, s1 == s1']
    mempty = Monotrans [(s,mempty,s) | s <- series]


-}

-- V2. 

-- Make it fast by using arrays.

data Monotrans s o = Monotrans (Array s (o,s))

toMono t = Monotrans $ listArray (minBound,maxBound) (map t [minBound..maxBound])

instance (Monoid o, Finite s) => Monoid (Monotrans s o) where
    mappend (Monotrans f) (Monotrans g) = Monotrans $ listArray bnds [(o <> o',s2) | s0 <- range bnds, let (o,s1) = f ! s0, let (o',s2) = g ! s1]
        where bnds = bounds f
    mempty = Monotrans $ listArray bnds [(mempty,s) | s <- series]
        where bnds = (minBound,maxBound)





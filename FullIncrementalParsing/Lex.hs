import Data.Monoid
import Data.Array

type Trans s o = s -> (s,o)

(<>) :: Monoid o => o -> o -> o
(<>) = mappend

-- The question: can we make transitions with output monoidal?

{-
-- Version 0: not useful, because the ouputs are not reusable


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

class Eq s => Finite s where
    series :: [s]


data Monotrans s o = Monotrans [(s,o,s)]

toMono t = Monotrans [(s,o,s') | s <- series, let (s',o) = t s]

instance (Monoid o, Finite s) => Monoid (Monotrans s o) where
    mappend (Monotrans f) (Monotrans g) = Monotrans [(s0,o <> o',s2) | (s0,o,s1) <- f, (s1',o',s2) <- g, s1 == s1']
    mempty = Monotrans [(s,mempty,s) | s <- series]


-}

-- V2. 

class Bounded s => Finite s


data Monotrans s o = Monotrans (Array s (o,s))

toMono t = Monotrans $ listArray (minBound,maxBound) (map t [minBound..maxBound])

instance (Monoid o, Finite s) => Monoid (Monotrans s o) where
    mappend (Monotrans f) (Monotrans g) = Monotrans $ listArray bnds [(o <> o',s2) | s0 <- range bnds, let (o,s1) = f ! s0, let (o',s2) <- g ! s1]
    mempty = Monotrans [(s,mempty,s) | s <- series]





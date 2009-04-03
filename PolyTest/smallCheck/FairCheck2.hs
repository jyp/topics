{-# LANGUAGE GeneralizedNewtypeDeriving, ScopedTypeVariables #-}
---------------------------------------------------------------------
-- SmallCheck: another lightweight testing library.
-- Colin Runciman, August 2006
-- Version 0.4, 23 May 2008
--
-- After QuickCheck, by Koen Claessen and John Hughes (2000-2004).
-- Modified by JP Bernardy
---------------------------------------------------------------------

module Test.SmallCheck 
-- (
--   smallCheck, smallCheckI, depthCheck, test,
--   Property, Testable,
--   forAll, forAllElem,
--   exists, existsDeeperBy, thereExists, thereExistsElem,
--   exists1, exists1DeeperBy, thereExists1, thereExists1Elem,
--   (==>),
--   Series, Serial(..),
--   (\/), (><), two, three, four,
--   cons0, cons1, cons2, cons3, 
--   alts0, alts1, alts2, alts3, 
--   N(..), Nat, Natural,
--   ) 
 where

import Control.Applicative
import List (intersperse)
import Monad (when)
import IO (stdout, hFlush)
import Foreign (unsafePerformIO)  -- used only for Testable (IO a)

------------------ <Series of depth-bounded values> -----------------

-- Series arguments should be interpreted as a depth bound (>=0)
-- Series results should have finite length

newtype Series a = Series {fromS :: [a]}
  deriving (Functor, Show)

instance Applicative Series where
    pure x = Series [x]
    Series f <*> Series x = Series (fairCross ($) f x)

instance Monad Series where
    return x = Series [x]
    x >>= f = Series (fairConcat $ map fromS $ map f $ fromS x)


instance Alternative Series where
    empty = Series []
    Series xs <|> Series ys = Series (interleave xs ys)

    

interleave (x:xs) ys = x:interleave ys xs
interleave []     ys = ys

fairConcat :: [[a]] -> [a]
fairConcat = concat . diags

fairCross f xs ys = fairConcat [[f x y | x <- xs] | y <- ys]

diags = diags'' []
    where diags'' xss yss0   = map head xss : case yss0 of 
                                      [] ->       diagsEnd (fnn $ map tail xss)  
                                      ys : yss -> diags''  (ys :   fnn (map tail xss))   yss

          diagsEnd [] = []
          diagsEnd xss = map head xss : fnn (map tail xss)

          fnn = filter (not . null)

------------------- <methods for type enumeration> ------------------

-- enumerated data values should be finite and fully defined
-- enumerated functional values should be total and strict

-- bounds:
-- for data values, the depth of nested constructor applications
-- for functional values, both the depth of nested case analysis
-- and the depth of results
 
class Serial a where
  series   :: Series a

class CoSerial a where
  coseries :: Series b -> Series (a -> b)

instance Serial () where
  series      = pure ()

instance CoSerial () where
  coseries rs = (\x () -> x) <$> rs

-- newtype Fix f = In {out :: f (Fix f)}

data Nat = Z | S Nat

toInt Z = 0
toInt (S n) = 1 + toInt n

instance Show Nat where
    show = show . toInt

instance Serial Nat where
    series = pure Z <|> S <$> series


--     coseries rs = constFun rs <|>
--                   (nat <$> rs <*> coseries rs)
--         where nat z f m = case m of
--                        Z -> z
--                        S x  -> f x
--               con z m = z
    

constFun rs = const <$> rs

{-
instance Serial Int where
  series      = [0..] \/ df (-1) 
     where df n = n : df (pred n)
  coseries rs = [ \i -> if i > 0 then f (N (i - 1))
                          else if i < 0 then g (N (abs i - 1))
                          else z
                  | z <- alts0 rs d, f <- alts1 rs d, g <- alts1 rs d ]
-}

mkPos [] = 1
mkPos (b:bs) = (if b then 1 else 0) + 2 * mkPos bs

instance Serial Integer where
  series = pure 0 <|> mkInt <$> series <*> series
    where mkInt sign bs = (if sign then negate else id) (mkPos bs)
          mkInt :: Bool -> [Bool] -> Integer

{-
newtype N a = N a
              deriving (Eq, Ord)

instance Show a => Show (N a) where
  show (N i) = show i

instance (Integral a, Serial a) => Serial (N a) where
  series      d = map N [0..d']
                  where
                  d' = fromInteger (toInteger d)
  coseries rs d = [ \(N i) -> if i > 0 then f (N (i - 1))
                              else z
                  | z <- alts0 rs d, f <- alts1 rs d ]

type Nat = N Int
type Natural = N Integer

instance Serial Float where
  series     d = [ encodeFloat sig exp
                 | (sig,exp) <- series d,
                   odd sig || sig==0 && exp==0 ]
  coseries rs d = [ f . decodeFloat
                  | f <- coseries rs d ]
             
instance Serial Double where
  series      d = [ frac (x :: Float)
                  | x <- series d ]
  coseries rs d = [ f . (frac :: Double->Float)
                  | f <- coseries rs d ]

frac :: (Real a, Fractional a, Real b, Fractional b) => a -> b
frac = fromRational . toRational

instance Serial Char where
  series      d = take (d+1) ['a'..'z']
  coseries rs d = [ \c -> f (N (fromEnum c - fromEnum 'a'))
                  | f <- coseries rs d ]

-}
instance (Serial a, Serial b) =>
         Serial (a,b) where
  series      = (,) <$> series <*> series


instance (CoSerial a, CoSerial b) => CoSerial (a,b) where
  coseries rs = uncurry <$> (coseries $ coseries rs)


instance (Serial a, Serial b, Serial c) =>
         Serial (a,b,c) where
  series      = (,,) <$> series <*> series <*> series

instance (CoSerial a, CoSerial b, CoSerial c) => CoSerial (a,b,c) where
  coseries rs = uncurry3 <$> (coseries $ coseries $ coseries rs)


instance (Serial a, Serial b, Serial c, Serial d) =>
         Serial (a,b,c,d) where
  series      = (,,,) <$> series <*> series <*> series <*> series
--  coseries rs = uncurry4 <$> (coseries $ coseries $ coseries $ coseries rs)

uncurry3 :: (a->b->c->d) -> ((a,b,c)->d)
uncurry3 f (x,y,z) = f x y z

uncurry4 :: (a->b->c->d->e) -> ((a,b,c,d)->e)
uncurry4 f (w,x,y,z) = f w x y z

{-
two   :: Series a -> Series (a,a)
two   s = s >< s

three :: Series a -> Series (a,a,a)
three s = \d -> [(x,y,z) | (x,(y,z)) <- (s >< s >< s) d]

four  :: Series a -> Series (a,a,a,a)
four  s = \d -> [(w,x,y,z) | (w,(x,(y,z))) <- (s >< s >< s >< s) d]

-}
cons0 :: a -> Series a
cons0 c = pure c

cons1 :: Serial a =>
         (a -> b) -> Series b
cons1 c = c <$> series

cons2 :: (Serial a, Serial b) =>
         (a->b->c) -> Series c
cons2 c = c <$> series <*> series

cons3 :: (Serial a, Serial b, Serial c) =>
         (a->b->c->d) -> Series d
cons3 c = c <$> series <*> series <*> series


alts0 ::  Series a -> Series a
alts0 s = s

alts1 ::  CoSerial a =>
            Series b -> Series (a->b)
alts1 bs = coseries bs


alts2 ::  (CoSerial a, CoSerial b) =>
            Series c -> Series (a->b->c)
alts2 cs = coseries (coseries cs)

alts3 ::  (CoSerial a, CoSerial b, CoSerial c) =>
            Series d -> Series (a->b->c->d)
alts3 ds = coseries (coseries (coseries ds))

alts4 ::  (CoSerial a, CoSerial b, CoSerial c, CoSerial d) =>
            Series e -> Series (a->b->c->d->e)
alts4 es = coseries (coseries (coseries (coseries es)))

instance Serial Bool where
  series        = cons0 False <|> cons0 True

instance CoSerial Bool where
  coseries rs = if_ <$> rs <*> rs
    where if_ a b x = if x then a else b


instance Serial a => Serial (Maybe a) where
  series        = cons0 Nothing <|> cons1 Just

instance CoSerial a => CoSerial (Maybe a) where
  coseries rs = maybe <$> alts0 rs <*> alts1 rs


instance (Serial a, Serial b) => Serial (Either a b) where
  series        = cons1 Left <|> cons1 Right

instance (CoSerial a, CoSerial b) => CoSerial (Either a b) where
  coseries rs =  either <$> alts1 rs <*> alts1 rs

instance Serial a => Serial [a] where
  series        = pure [] <|> cons2 (:)
  coseries rs = constFun rs <|> list <$> alts0 rs <*> alts2 rs
   where list y f xs = case xs of
                           []      -> y
                           (x:xs') -> f x xs'


-- Thanks to Ralf Hinze for the definition of coseries
-- using the nest auxiliary.

instance (CoSerial a, Serial b) => Serial (a -> b) where
  series = coseries series

instance (Serial a, CoSerial b) => CoSerial (a -> b) where
  coseries = cocoseries


cocoseries :: forall a b c. (Serial a, CoSerial b) => Series c -> Series ((a -> b) -> c)
cocoseries rs = Series
  [ \ f -> g [ f a | a <- args ] | g <- nest args ]
  where
    args :: [a]
    args = fromS series 

    nest :: [a] -> [[b] -> c]
    nest []     = [ \[] -> (c::c) | c <- fromS rs ]
    nest (a:as) = [ \(b:bs) -> f b bs | f <- fromS $ coseries $ Series (nest as) ]


-- show the extension of a function (in part, bounded both by
-- the number and depth of arguments)
instance (Serial a, Show a, Show b) => Show (a->b) where
  show f = 
    if maxarheight == 1
    && sumarwidth + length ars * length "->;" < widthLimit then
      "{"++(
      concat $ intersperse ";" $ [a++"->"++r | (a,r) <- ars]
      )++"}"
    else
      concat $ [a++"->\n"++indent r | (a,r) <- ars]
    where
    ars = take lengthLimit [ (show x, show (f x))
                           | x <- fromS series ]
    maxarheight = maximum  [ max (height a) (height r)
                           | (a,r) <- ars ]
    sumarwidth = sum       [ length a + length r 
                           | (a,r) <- ars]
    indent = unlines . map ("  "++) . lines
    height = length . lines
    (widthLimit,lengthLimit,depthLimit) = (80,5,3)::(Int,Int,Int)


newtype Property = Prop (Series Result)

data Result = Result {ok :: Bool, arguments :: [String]}
  deriving Show

result :: Result -> Property
result = Prop . pure

class Testable a where
    property :: a -> Property

instance Testable Bool where
    property b = Prop $ pure $ Result b []

instance Testable Property where
    property prop = prop

instance (Serial a, Show a, Testable b) => Testable (a -> b) where
    property f = forAll series f

evaluate :: Testable a => a -> Series Result
evaluate a = rs where Prop rs = property a


forAll :: (Show a, Testable b) => Series a -> (a->b) -> Property
forAll rs body = Prop $ do
    a <- rs
    res <- evaluate (body a)
    return (arg a res)
  where arg a res = res {arguments = show a : arguments res}


---------------------------


failures :: Testable a => a -> [Result]
failures a = filter (not . ok) $ fromS $ evaluate $ a


fairCheck :: Testable a => Int -> a -> [Result]
fairCheck n a = filter (not . ok) $ take n $ fromS $ evaluate $ a


fails :: [Integer] -> Bool
fails l = reverse l == l

testCommut :: Integer -> Integer -> Bool
testCommut a b = a + b == b + a
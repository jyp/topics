-- -----------------------------------------------------------------------------
-- 
-- CharSet.hs, part of Alex
--
-- (c) Chris Dornan 1995-2000, Simon Marlow 2003
--
-- An abstract CharSet type for Alex.  To begin with we'll use Alex's
-- original definition of sets as functions, then later will
-- transition to something that will work better with Unicode.
--
-- ----------------------------------------------------------------------------}

module CharSet (
  setSingleton,

  Byte,
  ByteSet,
  byteSetSingleton,
  byteRanges,
  byteSetRange,

  CharSet, -- abstract
  emptyCharSet,
  charSetSingleton,
  charSet,
  charSetMinus,
  charSetComplement,
  charSetRange,
  charSetUnion,
  charSetQuote,
  setUnions,
  byteSetToArray,
  byteSetElems,
  byteSetElem
  ) where

import Codec.Binary.UTF8.String

import Data.Array
import Data.Ranged
import Data.Word

type Byte = Word8
-- Implementation as functions
type CharSet = RSet Char
type ByteSet = RSet Byte
type Utf8Set = RSet [Byte]

emptyCharSet :: CharSet
emptyCharSet = rSetEmpty

byteSetElem :: ByteSet -> Byte -> Bool
byteSetElem = rSetHas

charSetSingleton :: Char -> CharSet
charSetSingleton = rSingleton

setSingleton :: DiscreteOrdered a => a -> RSet a
setSingleton = rSingleton

charSet :: [Char] -> CharSet
charSet = setUnions . fmap charSetSingleton

charSetMinus :: CharSet -> CharSet -> CharSet
charSetMinus = rSetDifference

charSetUnion :: CharSet -> CharSet -> CharSet
charSetUnion = rSetUnion

setUnions :: DiscreteOrdered a => [RSet a] -> RSet a
setUnions = foldr rSetUnion rSetEmpty

charSetComplement :: CharSet -> CharSet
charSetComplement = rSetNegation

charSetRange :: Char -> Char -> CharSet
charSetRange c1 c2 = makeRangedSet [Range (BoundaryBelow c1) (BoundaryAbove c2)]

byteSetToArray :: ByteSet -> Array Byte Bool
byteSetToArray set = array (fst (head ass), fst (last ass)) ass
  where ass = [(c,rSetHas set c) | c <- [0..0xff]]

byteSetElems :: ByteSet -> [Byte]
byteSetElems set = [c | c <- [0 .. 0xff], rSetHas set c]

charToUtf8Set :: CharSet -> Utf8Set
charToUtf8Set = makeRangedSet . concat . fmap (toUtfRange . mapR toUtf) . rSetRanges

toUtf c = encode [c]

toUtfRange (Range x BoundaryAboveAll) = toUtfRange (Range x (BoundaryAbove [0xFE, 0xBF, 0xBF, 0xBF]))
toUtfRange (Range BoundaryBelowAll x) = toUtfRange (Range (BoundaryAbove [0]) x)
toUtfRange (Range (BoundaryBelow x) (BoundaryBelow y)) = fix BoundaryBelow BoundaryBelow x y
toUtfRange (Range (BoundaryBelow x) (BoundaryAbove y)) = fix BoundaryBelow BoundaryAbove x y
toUtfRange (Range (BoundaryAbove x) (BoundaryBelow y)) = fix BoundaryAbove BoundaryBelow x y
toUtfRange (Range (BoundaryAbove x) (BoundaryAbove y)) = fix BoundaryAbove BoundaryAbove x y

fix a b x y 
    | length x == length y = [Range (a x) (b y)]
    | length x == 1 = Range (a x) (BoundaryAbove [0x7F]) : fix BoundaryBelow b [0xC1,0x80] y    
    | length x == 2 = Range (a x) (BoundaryAbove [0xCD,0xBF]) : fix BoundaryBelow b [0xE0,0xA0,0x80] y
    | length x == 3 = Range (a x) (BoundaryAbove [0xEF,0xBF,0xBF]) : fix BoundaryBelow b [0xF0,0x90,0x80,0x80] y


instance Functor Boundary where
    fmap f (BoundaryBelow a) = BoundaryBelow (f a)
    fmap f (BoundaryAbove a) = BoundaryAbove (f a)
    fmap _ BoundaryAboveAll = BoundaryAboveAll
    fmap _ BoundaryBelowAll = BoundaryBelowAll


mapR f (Range a b) = Range (fmap f a) (fmap f b)

byteRangeToBytePair :: Range [Byte] -> ([Byte],[Byte])
byteRangeToBytePair (Range x y) = (l x, h y)
    where l b = case b of
            BoundaryBelowAll -> error "panic: byteRangeToBytePair"
            BoundaryBelow a  -> a
            BoundaryAbove a  -> fmap (+ 1) a
            BoundaryAboveAll -> error "panic: byteRangeToBytePair"
          h b = case b of
            BoundaryBelowAll -> error "panic: byteRangeToBytePair"
            BoundaryBelow a  -> fmap (\x -> x - 1) a
            BoundaryAbove a  -> a
            BoundaryAboveAll -> error "panic: byteRangeToBytePair"

byteRanges :: CharSet -> [([Byte],[Byte])]
byteRanges =  (fmap byteRangeToBytePair) . rSetRanges . charToUtf8Set

byteSetRange :: Byte -> Byte -> ByteSet
byteSetRange c1 c2 = makeRangedSet [Range (BoundaryBelow c1) (BoundaryAbove c2)]

byteSetSingleton :: Byte -> ByteSet
byteSetSingleton = rSingleton

instance DiscreteOrdered Word8 where
    adjacent x y = x + 1 == y
    adjacentBelow 0 = Nothing
    adjacentBelow x = Just (x-1)

tt = charSetRange 'α' 'κ'

tt' = charToUtf8Set tt


-- TODO: More efficient generated code!
charSetQuote s = "(\\c -> " ++ foldr (\x y -> x ++ " || " ++ y) "False" (map quoteRange (rSetRanges s)) ++ ")" 
    where quoteRange (Range l h) = quoteL l ++ " && " ++ quoteH h
          quoteL (BoundaryAbove a) = "c > " ++ show a
          quoteL (BoundaryBelow a) = "c >= " ++ show a
          quoteL (BoundaryAboveAll) = "False"
          quoteL (BoundaryBelowAll) = "True"
          quoteH (BoundaryAbove a) = "c <= " ++ show a
          quoteH (BoundaryBelow a) = "c < " ++ show a
          quoteH (BoundaryAboveAll) = "True"
          quoteH (BoundaryBelowAll) = "False"


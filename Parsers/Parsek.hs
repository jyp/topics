{-# LANGUAGE RankNTypes #-}
{-

module Parsek
-------------------------------------------------------------------

Author:     Koen Claessen
Date:       2001-01-27
Compliance: hugs -98 (needs "forall" on types)
Licence:    GPL

Comments:

This module implements fast and space-efficient monadic parser
combinators. It is inspired by Daan Leijen's "Parsec" library.
The aim was to get a library that was equally fast, without
having to use the cumbersome "try" combinator. (That combinator
is still supported, but is defined to be the identity function.)
This aim is achieved by using a paralell choice combinator,
instead of using backtracking.

The result is a library that is nearly as fast as Daan's, and
is (almost) compatible with it. (The types in this module are
a bit more general than Daan's.)

A part of the code (the parser combinators like "many") is simply
taken from Daan's original code. I hope he doesn't mind :-)

-}

module Parsek
  -- basic parser type
  ( Parser        -- :: * -> * -> *; Functor, Monad, MonadPlus
  , Expect        -- :: *; = [String]
  , Unexpect      -- :: *; = [String]
  
  -- parsers
  , satisfy       -- :: Show s         => (s -> Bool) -> Parser s s
  , lookAhead     -- :: Show s         => (s -> Bool) -> Parser s s
  , string        -- :: (Eq s, Show s) => [s] -> Parser s [s]
  
  , char          -- :: Eq s => s -> Parser s s
  , noneOf        -- :: Eq s => [s] -> Parser s s
  , oneOf         -- :: Eq s => [s] -> Parser s s
  
  , spaces        -- :: Parser Char ()
  , space         -- :: Parser Char Char
  , newline       -- :: Parser Char Char
  , tab           -- :: Parser Char Char
  , upper         -- :: Parser Char Char
  , lower         -- :: Parser Char Char
  , alphaNum      -- :: Parser Char Char
  , letter        -- :: Parser Char Char
  , digit         -- :: Parser Char Char
  , hexDigit      -- :: Parser Char Char
  , octDigit      -- :: Parser Char Char
  , anyChar       -- :: Parser s s
  , anySymbol     -- :: Parser s s

  -- parser combinators
  , label         -- :: String -> Parser s a -> Parser s a
  , (<?>)         -- :: String -> Parser s a -> Parser s a
  , pzero         -- :: Parser s a
  , (<|>)         -- :: Parser s a -> Parser s a -> Parser s a
  , try           -- :: Parser s a -> Parser s a; = id
  , choice        -- :: [Parser s a] -> Parser s a
  , option        -- :: a -> Parser s a -> Parser s a
  , optional      -- :: Parser s a -> Parser s ()
  , between       -- :: Parser s open -> Parser s close -> Parser s a -> Parser s a
  , count         -- :: Int -> Parser s a -> Parser s [a]

  , chainl1       -- :: Parser s a -> Parser s (a -> a -> a) -> Parser s a
  , chainl        -- :: Parser s a -> Parser s (a -> a -> a) -> a -> Parser s a
  , chainr1       -- :: Parser s a -> Parser s (a -> a -> a) -> Parser s a
  , chainr        -- :: Parser s a -> Parser s (a -> a -> a) -> a -> Parser s a
                
  , skipMany1     -- :: Parser s a -> Parser s ()
  , skipMany      -- :: Parser s a -> Parser s ()
  , many1         -- :: Parser s a -> Parser s [a]
  , many          -- :: Parser s a -> Parser s [a]
  , sepBy1        -- :: Parser s a -> Parser s sep -> Parser s [a]
  , sepBy         -- :: Parser s a -> Parser s sep -> Parser s [a]
  
  -- parsing & parse methods
  , ParseMethod   -- :: * -> * -> * -> *
  , ParseResult   -- :: * -> * -> *; = Either (Maybe s, Expect, Unexpect) r
  , parseFromFile -- :: Parser Char a -> ParseMethod Char a r -> FilePath -> IO (ParseResult Char r)
  , parse         -- :: Parser s a -> ParseMethod s a r -> [s] -> ParseResult s r

  , shortestResult             -- :: ParseMethod s a a
  , longestResult              -- :: ParseMethod s a a
  , longestResults             -- :: ParseMethod s a [a]
  , allResults                 -- :: ParseMethod s a [a]
  , completeResults            -- :: ParseMethod s a [a]
  
  , shortestResultWithLeftover -- :: ParseMethod s a (a,[s])
  , longestResultWithLeftover  -- :: ParseMethod s a (a,[s])
  , longestResultsWithLeftover -- :: ParseMethod s a ([a],[s])
  , allResultsWithLeftover     -- :: ParseMethod s a [(a,[s])]
  )
 where
  
import Monad
  ( MonadPlus(..)
  )

import List
  ( union
  , intersperse
  )

import Char

infix  0 <?>
infixr 1 <|>

-------------------------------------------------------------------------
-- type Parser

newtype Parser s a
  =  Parser {fromP :: forall res. (a -> Expect -> P s res) -> Expect -> P s res}

-- type P; parsing processes

data P s res
  = Symbol (s -> P s res)
  | Fail Expect Unexpect
  | Result res (P s res)

-- type Expect, Unexpect

type Expect
  = [String]

type Unexpect
  = [String]

-------------------------------------------------------------------------
-- instances: Functor, Monad, MonadPlus

instance Functor (Parser s) where
  fmap p (Parser f) =
    Parser (\fut -> f (fut . p))

instance Monad (Parser s) where
  return a =
    Parser (\fut -> fut a)
  
  Parser k >>= f =
    -- Parser (k (fromP . f))
    Parser (\fut -> k (\a -> fromP (f a) fut))

  fail s =
    Parser (\fut exp -> Fail exp [s])

instance MonadPlus (Parser s) where
  mzero =
    Parser (\fut exp -> Fail exp [])
    
  mplus (Parser f) (Parser g) =
    Parser (\fut exp -> f fut exp `plus` g fut exp)

plus :: P s res -> P s res -> P s res
Symbol fut1    `plus` Symbol fut2    = Symbol (\s -> fut1 s `plus` fut2 s)
Fail exp1 err1 `plus` Fail exp2 err2 = Fail (exp1 `union` exp2) (err1 `union` err2)
p              `plus` Result res q   = Result res (p `plus` q)
Result res p   `plus` q              = Result res (p `plus` q)
p@(Symbol _)   `plus` _              = p
_              `plus` q@(Symbol _)   = q

-------------------------------------------------------------------------
-- primitive parsers

anySymbol :: Parser s s
anySymbol =
  Parser (\fut exp -> Symbol (\c ->
    fut c []
  ))

satisfy :: Show s => (s -> Bool) -> Parser s s
satisfy pred =
  Parser (\fut exp -> Symbol (\c ->
    if pred c
      then fut c []
      else Fail exp [show c]
  ))

label :: Parser s a -> String -> Parser s a
label (Parser f) s =
  Parser (\fut exp ->
    if null exp
      then f (\a _ -> fut a []) [s]
      else f fut exp
  )

lookAhead :: Parser s s
lookAhead =
  Parser (\fut exp -> Symbol (\c ->
    feed c (fut c [])
  ))
 where
  feed c (Symbol sym)     = sym c
  feed c (Result res fut) = Result res (feed c fut)
  feed c p@(Fail _ _)     = p

-- specialized

string :: (Eq s, Show s) => [s] -> Parser s [s]
string s =
  Parser (\fut exp ->
    let inputs []     = fut s []
        inputs (x:xs) =
          Symbol (\c ->
            if c == x
              then inputs xs
              else Fail (if null exp then [show s] else exp) [show c]
          )
     
     in inputs s
  )

-------------------------------------------------------------------------
-- derived parsers

char c    = satisfy (==c)         <?> show [c]
noneOf cs = satisfy (\c -> not (c `elem` cs))
oneOf cs  = satisfy (\c -> c `elem` cs)

spaces    = skipMany space        <?> "white space"
space     = satisfy (isSpace)     <?> "space"
newline   = char '\n'             <?> "new-line"
tab       = char '\t'             <?> "tab"
upper     = satisfy (isUpper)     <?> "uppercase letter"
lower     = satisfy (isLower)     <?> "lowercase letter"
alphaNum  = satisfy (isAlphaNum)  <?> "letter or digit"
letter    = satisfy (isAlpha)     <?> "letter"
digit     = satisfy (isDigit)     <?> "digit"
hexDigit  = satisfy (isHexDigit)  <?> "hexadecimal digit"
octDigit  = satisfy (isOctDigit)  <?> "octal digit"
anyChar   = anySymbol

-----------------------------------------------------------
-- parser combinators

(<?>) :: Parser s a -> String -> Parser s a
p <?> s = label p s

pzero :: Parser s a
pzero = mzero

(<|>) :: Parser s a -> Parser s a -> Parser s a
p <|> q = p `mplus` q

try :: Parser s a -> Parser s a
try p = p -- backwards compatibility with Parsec

choice :: [Parser s a] -> Parser s a
choice ps = foldr (<|>) mzero ps

option :: a -> Parser s a -> Parser s a
option x p = p <|> return x

optional :: Parser s a -> Parser s ()
optional p = (do p; return ()) <|> return ()

between :: Parser s open -> Parser s close -> Parser s a -> Parser s a
between open close p = do open; x <- p; close; return x

-- repetition
                
skipMany1,skipMany :: Parser s a -> Parser s ()
skipMany1 p = do p; skipMany p
skipMany  p = let scan = (do p; scan) <|> return () in scan

many1,many :: Parser s a -> Parser s [a]
many1 p = do x <- p; xs <- many p; return (x:xs)
many  p = let scan f = (do x <- p; scan (f.(x:))) <|> return (f []) in scan id

sepBy1,sepBy :: Parser s a -> Parser s sep -> Parser s [a]
sepBy  p sep = sepBy1 p sep <|> return []
sepBy1 p sep = do x <- p; xs <- many (do sep; p); return (x:xs)

count :: Int -> Parser s a -> Parser s [a]
count n p = sequence (replicate n p)

chainr,chainl :: Parser s a -> Parser s (a -> a -> a) -> a -> Parser s a
chainr p op x = chainr1 p op <|> return x
chainl p op x = chainl1 p op <|> return x

chainr1,chainl1 :: Parser s a -> Parser s (a -> a -> a) -> Parser s a
chainr1 p op = scan
 where
  scan   = do x <- p; rest x
  rest x = (do f <- op; y <- scan; return (f x y)) <|> return x

chainl1 p op = scan
 where
  scan   = do x <- p; rest x
  rest x = (do f <- op; y <- p; rest (f x y)) <|> return x
                              
-------------------------------------------------------------------------
-- type ParseMethod, ParseResult

type ParseMethod s a r
  = P s a -> [s] -> ParseResult s r

type ParseResult s r
  = Either (Maybe s, Expect, Unexpect) r

-- parse functions

parseFromFile :: Parser Char a -> ParseMethod Char a r -> FilePath -> IO (ParseResult Char r)
parseFromFile p method file =
  do s <- readFile file
     return (parse p method s)

parse :: Parser s a -> ParseMethod s a r -> [s] -> ParseResult s r
parse (Parser f) method xs =
  method (f (\a exp -> Result a (Fail exp [])) []) xs

-- parse methods

shortestResult :: ParseMethod s a a
shortestResult p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res _) _      = Right res
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err

longestResult :: ParseMethod s a a
longestResult p xs = scan p Nothing xs
 where
  scan (Symbol sym)   mres       (x:xs) = scan (sym x) mres xs
  scan (Symbol _)     mres       []     = scan (Fail [] []) mres []
  scan (Result res p) _          xs     = scan p (Just res) xs
  scan (Fail exp err) Nothing    (x:xs) = failSym x exp err
  scan (Fail exp err) Nothing    []     = failEof exp err
  scan (Fail _ _)     (Just res) _      = Right res

longestResults :: ParseMethod s a [a]
longestResults p xs = scan p [] [] xs
 where
  scan (Symbol sym)   []  old (x:xs) = scan (sym x) [] old xs
  scan (Symbol sym)   new old (x:xs) = scan (sym x) [] new xs
  scan (Symbol _)     new old []     = scan (Fail [] []) new old []
  scan (Result res p) new old xs     = scan p (res:new) [] xs
  scan (Fail exp err) []  []  (x:xs) = failSym x exp err
  scan (Fail exp err) []  []  []     = failEof exp err
  scan (Fail _ _)     []  old _      = Right old
  scan (Fail _ _)     new _   _      = Right new
 
allResults :: ParseMethod s a [a]
allResults p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res p) xs     = Right (res : scan' p xs)
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err

  scan' p xs =
    case scan p xs of
      Left  _    -> []
      Right ress -> ress

completeResults :: ParseMethod s a [a]
completeResults p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res p) []     = Right (res : scan' p [])
  scan (Result _ p)   xs     = scan p xs
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err

  scan' p xs =
    case scan p xs of
      Left  _    -> []
      Right ress -> ress

-- with left overs

shortestResultWithLeftover :: ParseMethod s a (a,[s])
shortestResultWithLeftover p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res _) xs     = Right (res,xs)
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err

longestResultWithLeftover :: ParseMethod s a (a,[s])
longestResultWithLeftover p xs = scan p Nothing xs
 where
  scan (Symbol sym)   mres         (x:xs) = scan (sym x) mres xs
  scan (Symbol _)     mres         []     = scan (Fail [] []) mres []
  scan (Result res p) _            xs     = scan p (Just (res,xs)) xs
  scan (Fail exp err) Nothing      (x:xs) = failSym x exp err
  scan (Fail exp err) Nothing      []     = failEof exp err
  scan (Fail _ _)     (Just resxs) _      = Right resxs

longestResultsWithLeftover :: ParseMethod s a ([a],Maybe [s])
longestResultsWithLeftover p xs = scan p empty empty xs
 where
  scan (Symbol sym)   ([],_) old    (x:xs) = scan (sym x) empty old xs
  scan (Symbol sym)   new    old    (x:xs) = scan (sym x) empty new xs
  scan (Symbol _)     new    old    []     = scan (Fail [] []) new old []
  scan (Result res p) (as,_) old    xs     = scan p (res:as,Just xs) empty xs
  scan (Fail exp err) ([],_) ([],_) (x:xs) = failSym x exp err
  scan (Fail exp err) ([],_) ([],_) []     = failEof exp err
  scan (Fail _ _)     ([],_)  old _        = Right old
  scan (Fail _ _)     new _   _            = Right new
 
  empty = ([],Nothing)
 
allResultsWithLeftover :: ParseMethod s a [(a,[s])]
allResultsWithLeftover p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res p) xs     = Right ((res,xs) : scan' p xs)
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err

  scan' p xs =
    case scan p xs of
      Left  _    -> []
      Right ress -> ress

-- failing

failSym :: s -> Expect -> Unexpect -> ParseResult s r
failSym s exp err = Left (Just s, exp, err)

failEof :: Expect -> Unexpect -> ParseResult s r
failEof exp err = Left (Nothing, exp, err)

-------------------------------------------------------------------------
-- the end.


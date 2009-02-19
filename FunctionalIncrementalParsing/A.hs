import Code
import Data.Char

data Expr = Int Int | Add Expr Expr | Mul Expr Expr | Paren Expr | Err String
  deriving Show

failure = Yuck $ Symb failure (const failure)
eof = Symb unit (const $ Yuck eof)

many v = some v `Disj` Pure []
some v = Pure (:) :*: v :*: many v
sepBy1 p s  = Pure (:) :*: p :*: many (s *> p)

expr lvl op c el = please 2 (foldr1 op <$> sepBy1 el (symbol lvl c)) (Err $ "not a " ++ [c] ++ "-expr") 

factors = expr 5 Mul '*' atom
terms = expr 5 Add '+' factors

int = (Int . read) <$> some (digit 10)

paren = Paren <$> (symbol 10 '(' *> terms <* symbol 5 ')')

atom = int <|> paren


digit lvl = satisfy lvl (isDigit) '0'

please lvl p d = p <|> power lvl Yuck (Pure d)


satisfy lvl f def  = Symb err (\s ->if f s then Pure s else err)
    where err = power lvl Yuck $ Pure def

power 0 f = id
power n f = f . power (n-1) f

symbol lvl s = satisfy lvl (== s) s


unit = Pure ()

(<|>) = Disj
f <$> p = Pure f <*> p
(<*>) = (:*:)
a *> b = Pure (flip const) :*: a :*: b
a <* b = Pure const :*: a :*: b


test p = runParser (p <* eof)
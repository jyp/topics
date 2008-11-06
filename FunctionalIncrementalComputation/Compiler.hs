{-# OPTIONS -i../Machines #-}
import SuspensionVM 
import Control.Applicative
import Data.Char

data Term = Bin Term (Int -> Int -> Int) Term | Con Int

data ByteCode = App (Int -> Int -> Int) | Push Int

scan = case_ (error "unexpected eof!") (\s -> pure s)

expect s0 = case_ (error "unexpected eof!") (\s -> if s /= s0 then error "expected ..." else pure ())

parseAtom = case_ (error "eof!") $
  \s -> case s of
      '(' -> parseExpr <* expect ')'
      c -> pure $ Con (ord c - ord '0')

parseOp = expect '+' *> pure (+) 

-- whoops, we need monad interface :( (and look ahead)
parseExpr = do
  a <- parseAtom
  case parseOp of
     Nothing -> return a
     Just x -> Bin <$> parseAtom <*> parseOp <*> parseExpr
      
  


      
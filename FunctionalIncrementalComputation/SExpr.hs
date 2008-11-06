import SuspensionVM hiding (Tree, toTree, Leaf,Node)

import Control.Applicative
import Data.Tree

data SExpr = Cons SExpr SExpr | Leaf Char | Tip
   deriving Show

eof = case_ (pure ()) (error "expected eof")

readSExpr :: P Char SExpr
readSExpr = case_ (error "unexpected end of input") $
           \s -> case s of
               ':' -> Cons <$> readSExpr <*> readSExpr
               '.' -> pure Tip
               c ->  pure $ Leaf c


toForest (Cons l r) = toTree l : toForest r
toForest (Leaf c) = [Node [c] []]
toForest Tip  = []

toTree (Leaf c) = Node [c] []
toTree t = Node "*" (toForest t)

sampleInput = ":a:b::c:d:e.:f:g:h.asdfs"
sampleResult = -- drawForest $ toForest $ 
               hd $ evalR sampleInput $ fromP ((,) <$> readSExpr <*> eof) Done




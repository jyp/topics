\ignore{

\begin{code}
module SExpr where
import Control.Applicative
import Data.Tree
\end{code}

}

\begin{code}
data SExpr = S [SExpr] | Atom Char
\end{code}

\ignore{

data SExpr = S [SExpr] (Maybe Char) | Atom Char | Quoted [SExpr] (Maybe Char) | Inserted Char | Deleted Char

showS _ (Atom c) = [c]
showS ([open,close]:ps) (S cl) = open : concatMap (showS ps) s ++ [close]

instance Show SExpr where
    show = showS (cycle ["()","[]","{}"])

parseList :: Parser Char [SExpr]
parseList = Symb
   (Pure [])
   (\c -> case c of
       ' '  -> parseList -- ignore spaces
       '('  -> Pure (\h t -> S h : t) :*: parseList :*: parseList
       c    -> Pure (Atom c :) :*: parseList)


-----


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


}
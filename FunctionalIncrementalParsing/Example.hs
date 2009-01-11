import Parsers.Incremental
import Control.Applicative
------------------------------------------------------------
-- Examples

data SExpr = S [SExpr] (Maybe Char) | Atom Char | Quoted [SExpr] (Maybe Char) | Inserted Char | Deleted Char
    deriving Show
-- the only place we use disjunction is in many.

symb n c = Look (Shif n) (Shif . c)

manyx v = some v <|> oops "closing..." (pure [])
somex v = (:) <$> v <*> manyx v

parseExpr = symb
     (oops "no input" $ pure (Inserted '?')) 
     -- empty
     (\c ->case c of 
         '(' -> S <$> many parseExpr <*> closing ')'
         ')' -> oops ("unmatched )") $ pure $ Deleted ')'
         c   -> pure $ Atom c)

closing close = symb
     (oops "not closed" $ pure Nothing)
     -- empty
     (\c ->if c == close then pure (Just ')')
                         else oops ("closed with: " ++ show c) $ pure (Just c)
     )

eof' = symb (pure ()) (\_ -> oops "eof expected!" eof')

test = mkProcess (parseExpr <* eof')


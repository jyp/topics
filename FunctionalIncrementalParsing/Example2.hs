import Code
------------------------------------------------------------
-- Examples

data SExpr = S [SExpr] (Maybe Char) | Atom Char | Quoted [SExpr] (Maybe Char) | Missing | Deleted Char
    deriving Show
-- the only place we use disjunction is in many.

symb = Symb
oops _ = Yuck
pure = Pure
f <$> x = pure f <*> x
(<*>) = (:*:)
(<|>) = (:|:)
x <* y = const <$> x <*> y

many v = some v <|> pure []
some v = (:) <$> v <*> many v

parseExpr = symb
     (oops "no input" $ pure Missing) 
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


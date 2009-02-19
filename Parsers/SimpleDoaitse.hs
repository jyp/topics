{-# LANGUAGE RankNTypes, GADTs, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}
module Main where
import Prelude hiding (fail)
import Debug.Trace
import Maybe

import Control.Applicative

ap f a = f a 

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Classes     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

class (Applicative a, Alternative a) => AA a

class symbol `Describes`  token where
       eqSymTok     ::  symbol  -> token -> Bool

class  Symbol p symbol token | symbol -> token where
  pSym  ::  symbol -> p token

type Strings = [String]

type Cost = Int
type Progress = Int

class  Provides state symbol token | state symbol -> token  where
       splitState   ::  symbol -> state   -> Maybe (token, state, Progress)
       insertSym    ::  symbol             -> state            ->  Strings -> Maybe (Cost, token,  state)
       deleteTok    ::  symbol  -> token   -> state ->  state  ->  Strings -> Maybe (Cost,         state) 

class Eof state where
       eof          ::  state   -> Bool
       deleteAtEnd  ::  state   -> Maybe (Cost, state)

class  Parser p  where
       parse  ::   Eof state => p state a -> state -> a

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Steps      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

data  Steps   a  where
      Step   ::              Progress       ->  Steps a                                -> Steps   a
      Fail   ::              [String]       ->  [[String]  -> Maybe (Int, Steps   a)]  -> Steps   a
      Apply  ::  forall b.   (b -> a)       ->  Steps   b                              -> Steps   a
      End_h  ::              ([a] , [a] -> Steps r)        ->  Steps   (a,r)           -> Steps   (a, r)
      End_f  ::              [Steps   a]   ->  Steps   a                               -> Steps   a


fail        =  Fail [] [const (Just (0, fail))]
noAlts      =  Fail [] []

eval :: Steps   a      ->  a
eval (Step  _    l)     =   eval l
eval (Fail   ss  ls  )  =   eval (getCheapest 3 [ c | f <- ls, let Just c = f ss]) -- catMaybes $ map ($ss) ls))
eval (Apply  f   l   )  =   f (eval l)
eval (End_f   _  _   )  =   error "dangling End_f constructor"
eval (End_h   _  _   )  =   error "dangling End_h constructor"

push    :: v -> Steps   r -> Steps   (v, r)
push v  =  Apply ((,) v)
apply   :: Steps (b -> a, (b, r)) -> Steps (a, r)
apply   =  Apply (\(b2a, ~(b, r)) -> (b2a b, r))  

norm ::  Steps   a                   ->  Steps   a
norm    (Apply f (Step   p    l  ))   =   Step p (Apply f l)
norm    (Apply f (Fail   ss   ls ))   =   Fail ss (applyFail (Apply f) ls)
norm    (Apply f (Apply  g    l  ))   =   norm (Apply (f.g) l)
norm    (Apply f (End_f  ss   l  ))   =   End_f (map (Apply f) ss) (Apply f l)
norm    (Apply f (End_h  _    _  ))   =   error "Apply before End_h"
norm    steps                         =   steps

applyFail f  = map (\ g -> \ ex -> case g ex of
                                   Just (c, l) -> Just (c, f l)
                                   Nothing -> Nothing)

best :: Steps   a -> Steps   a -> Steps   a
x `best` y =   norm x `best'` norm y

best' :: Steps   b -> Steps   b -> Steps   b
Fail  sl  ll     `best'`  Fail  sr rr     =   Fail (sl ++ sr) (ll++rr)
Fail  _   _      `best'`  r               =   r
l                `best'`  Fail  _  _      =   l
Step  n   l      `best'`  Step  m  r
    | n == m                              =   Step n (l `best'` r)     
    | n < m                               =   Step n (l  `best'`  Step (m - n)  r)
    | n > m                               =   Step m (Step (n - m)  l  `best'` r)
End_f  as  l            `best'`  End_f  bs r     =   End_f (as++bs)  (l `best` r)
End_f  as  l            `best'`  r               =   End_f as        (l `best` r)
l                       `best'`  End_f  bs r     =   End_f bs        (l `best` r)
End_h  (as, k_h_st)  l  `best'`  End_h  (bs, _) r     =   End_h (as++bs, k_h_st)  (l `best` r)
End_h  as  l            `best'`  r               =   End_h as (l `best` r)
l                       `best'`  End_h  bs r     =   End_h bs (l `best` r)
l                       `best'`  r               =   l `best` r 

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% History     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- do not change into data !!
newtype  P_h    st  a   =  P_h  (forall r h     .  ( (  h, a)  ->  st -> Steps   r) 
                                                ->      h      ->  st -> Steps   r)
unP_h (P_h p) = p

instance Applicative (P_h  state) where
  (P_h p) <*> (P_h q)  =  P_h  (\  k -> p $ q $ \ ((h, b2a), b) -> k (h, b2a b))
  pure a            =  P_h  (\  k h  st  -> k (h, a) st)

instance Alternative (P_h  state) where
  (P_h p) <|> (P_h q)  =  P_h  (\  k h inp  -> p k h inp `best` q k h inp) 
  empty                =  P_h  (\  k _  _   -> noAlts) 

instance Functor (P_h state) where
    f `fmap` (P_h p)      =  P_h  (\  k -> p  $ \ (h, a)  -> k (h, f a)) 


instance  (  Show symbol
          ,  symbol `Describes` token
          ,  Provides state symbol token) => Symbol (P_h  state) symbol token where
  pSym a =  P_h (  let p = \ k  h inp ->  
                        let ins ex =  case insertSym a inp ex of
                                      Just  (c_i, v,  st_i) ->  Just (c_i, k (h, v) st_i)
                                      Nothing               ->  Nothing
                            del s ss ex  =  case deleteTok a s ss inp ex of
                                            Just  (c_d, st_d) ->  Just (c_d,  p k h st_d)
                                            Nothing           ->  Nothing
                        in  case splitState a inp of
                            Just (s, ss, pr)   ->  if a `eqSymTok` s  
                                                   then  Step pr (k (h,s) ss) 
                                                   else  Fail [show a] [ins, del s ss]                                               
                            Nothing       ->             Fail [show a] [ins]
                   in p)

data Id a = Id a deriving Show

instance   Parser P_h  where
  parse (P_h p)
   =  fst . eval . p  (\ r rest -> if eof rest then push (snd r) fail else error "pEnd_fmissing?") undefined 

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Future      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- do not change into data !!
newtype  P_f st a  = P_f (forall r . (st -> Steps   r) -> st -> Steps   (a, r))
unP_f (P_f p) = p

instance Applicative (P_f st) where
 P_f p  <*>  P_f q  =   P_f ( (apply .) . (p .q))
 pure a          =   P_f ((push a).)

instance Alternative (P_f st) where
 P_f p  <|>  P_f q  =   P_f (\ k inp  -> p k inp `best` q k inp)  
 empty              =   P_f (\ k inp  -> noAlts)
instance Functor (P_f st) where
    fmap f = (pure f <*>)

instance  (Show symbol, Describes symbol token, Provides state symbol token) =>  Symbol (P_f  state) symbol token where
  pSym a =  P_f (  let p = \ k inp ->  
                        let ins ex =  case insertSym a inp ex of
                                      Just  (c_i, v,  st_i) ->  Just  (c_i, push v (k st_i))
                                      Nothing               ->  Nothing
                            del s ss ex  =  case deleteTok a s ss inp ex of
                                            Just  (c_d, st_d) ->  Just (c_d,  p k  st_d)
                                            Nothing           ->  Nothing
                        in  case splitState a inp of
                            Just (s, ss, pr)   ->  if a `eqSymTok` s  
                                                   then  Step pr (push s (k ss)) 
                                                   else  Fail [show a] [ins, del s ss]                                              
                            Nothing       ->             Fail [show a] [ins]
                   in p)

instance  Parser P_f  where
  parse (P_f p) =  fst . eval . p (\ rest -> if eof rest then fail else error "end missing")

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Monads      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

infixr 1 >>>=
class GenMonad  m_1 m_2 where
   (>>>=) :: m_1 b -> ( b -> m_2  a) -> m_2 a

instance     Monad (P_h  state) 
         =>  GenMonad (P_h  state) (P_h state) where
  (>>>=)  = (>>=) --  the monadic bind defined before

instance GenMonad (P_h  state) (P_f  state) where
  (P_h p)  >>>= pv2q 
           = P_f (\ k st -> p (\ ((), pv) st -> unP_f (pv2q pv) k st) () st)

newtype P_m state a = P_m (P_h  state a, P_f state a) 
unP_m_h (P_m  (P_h h,  _    ))  =  h
unP_m_f (P_m  (_    ,  P_f f))  =  f

instance  (Applicative (P_h  st), Applicative (P_f  st)) =>  Applicative (P_m  st) where
 P_m (hp, fp)  <*> P_m ~(hq, fq)   = P_m  (hp <*> hq, fp <*> fq) 
 pure a                         = P_m  (pure a, pure a) 
instance  (Alternative (P_h  st), Alternative (P_f  st)) =>  Alternative (P_m  st) where
 P_m (hp, fp)  <|> P_m (hq, fq)    = P_m  (hp <|> hq, fp <|> fq)
 empty                             = P_m  (empty,         empty)       
instance AA (P_m st) where
instance Functor (P_m st) where
    fmap f = (pure f <*>)
 
instance  (Show symbol, Describes symbol token, Provides state symbol token)  => Symbol (P_m state) symbol token where
  pSym a =  P_m (pSym a, pSym a)

instance   Parser P_m  where
  parse (P_m (_, (P_f fp)))  
      =  fst . eval . fp (\ rest -> if eof rest  then fail else error "End_fmissing?") 

instance AA (P_h state) => Monad (P_h state) where
  P_h p >>= a2q  = P_h ( \ k -> p (\ (h, a) st -> unP_h (a2q a) k h st))
  return     = pure

instance AA (P_m st) => Monad (P_m st) where
     P_m  (P_h p, _)  >>=  a2q = trace "bind " (
           P_m  (  P_h   (\k -> p (\ (h ,a) i -> unP_m_h (a2q a) k h i)     )
                ,  P_f  (\k inp -> trace "calling p" $ p (\ (_,a) i  -> unP_m_f (a2q a) k i) () inp ))
                )
     return  = pure 

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Greedy      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

best_gr :: Steps a -> Steps a -> Steps a

l@  (Step _ _)   `best_gr` _  = l
l                `best_gr` r  = l `best` r

class  Greedy p where 
  (<<|>) :: p a -> p a -> p a

instance Greedy (P_h state)  where
  P_h p <<|> P_h q = P_h (\ k h st  -> norm (p k h  st) `best_gr` norm (q k h  st))

instance Greedy (P_f state)  where
  P_f p <<|> P_f q = P_f (\ k   st  -> norm (p k    st) `best_gr` norm(q k     st))

instance Greedy (P_m state) where
    P_m (hp, fp)  <<|> P_m (hq, fq) = P_m  (hp <<|> hq, fp <<|> fq) 


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Ambiguous   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

class Ambiguous p where
 amb :: p a -> p [a]

instance Ambiguous (P_h state) where
  amb (P_h p) = P_h ( \k h st ->  removeEnd_h $ p (\ (h,a) st' -> End_h ([a], \ as -> k (h,as) st') noAlts) h st)
removeEnd_h     :: Steps (a, r) -> Steps r
removeEnd_h (Fail  m ls             )  =   Fail m (applyFail removeEnd_h ls)
removeEnd_h (Step  ps l             )  =   Step  ps (removeEnd_h l)
removeEnd_h (Apply f l              )  =   error "not in history parsers"
removeEnd_h (End_h  (as, k_h_st) r  )  =   k_h_st as `best` removeEnd_h r 


instance Ambiguous (P_f state) where
  amb (P_f p) = P_f (\k inp -> combinevalues . removeEnd_f $ p (\st -> End_f [k st] noAlts) inp)
removeEnd_f      :: Steps r -> Steps [r]
removeEnd_f (Fail m ls)        =   Fail m (applyFail  removeEnd_f ls)
removeEnd_f (Step ps l)        =   Step ps (removeEnd_f l)
removeEnd_f (Apply f l)        =   Apply (map' f) (removeEnd_f l)
removeEnd_f (End_f(s:ss) r)    =   Apply  (:(map  eval ss)) s 
                                                 `best`
                                          removeEnd_f r

combinevalues  :: Steps [(a,r)] -> Steps ([a],r)
combinevalues lar           =   Apply (\ lar -> (map fst lar, snd (head lar))) lar
map' f ~(x:xs)              =   f x : map f xs

instance (Ambiguous (P_h state), Ambiguous (P_f state)) => Ambiguous (P_m state) where
  amb  (P_m (hp, fp))  = P_m (amb hp, amb fp)
       
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% getCheapest  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

getCheapest :: Int -> [(Int, Steps a)] -> Steps a 
getCheapest _ [] = error "no correcting alternative found"
getCheapest n l  =  snd $  foldr (\(w,ll) btf@(c, l)
                               ->    if w < c 
                                     then let new = (traverse n ll w c) 
                                          in if new < c then (new, ll) else btf
                                     else btf 
                               )   (maxBound, error "getCheapest") l


traverse :: Int -> Steps a -> Int -> Int -> Int
traverse 0 _                =  \ v c ->  v
traverse n (Step ps l)      =  traverse (n-1) l
traverse n (Apply _ l)      =  traverse n     l
traverse n (Fail m m2ls)    =  \ v c ->  foldr (\ (w,l) c' -> if v + w < c' then traverse (n-1) l (v+w) c'
                                                                            else c'
                                               ) c (catMaybes $ map ($m) m2ls)
traverse n (End_h ((a, lf))    r)  =  traverse n (lf a `best` removeEnd_h r)
traverse n (End_f (l      :_)  r)  =  traverse n (l `best` r)   


-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% pErrors     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

class state `Stores`  errors where
  getErrors    ::  state   -> (errors, state)

class  p `AsksFor` errors where
  pErrors :: p errors
  pEnd    :: p errors

instance (Eof state, Stores state errors) =>  AsksFor (P_h state) errors where
  pErrors = P_h (\ k h inp -> let (errs, inp') = getErrors inp
                              in k (h, errs) inp')
  pEnd    = P_h (\ k h inp -> let deleterest inp =  case deleteAtEnd inp of
                                                    Nothing -> let (finalerrors, finalstate) = getErrors inp
                                                               in k (h, finalerrors) finalstate
                                                    Just (i, inp') -> Fail []  [const (Just (i,  deleterest inp'))]
                              in deleterest inp
                )

instance (Eof state, Stores state errors) => AsksFor (P_f state) errors where
  pErrors = P_f (\ k   inp -> let (errs, inp') = getErrors inp
                              in push errs (k inp'))
  pEnd    = P_f (\ k   inp -> let deleterest inp =  case deleteAtEnd inp of
                                                    Nothing -> let (finalerrors, finalstate) = getErrors inp
                                                               in push finalerrors (k finalstate)
                                                    Just (i, inp') -> Fail [] [const (Just (i, deleterest inp'))]
                              in deleterest inp
                )

instance  (state `Stores` errors, Eof state) => AsksFor (P_m state)  errors where
  pErrors   = P_m  (pErrors,  pErrors)
  pEnd      = P_m  (pEnd,     pEnd)

{-
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Microsteps  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


class MicroStep result where
  microstep :: result a -> result a

instance MicroStep Steps where
   microstep steps = Micro steps

class Micro p where
  micro :: p a -> p a

instance  Micro (P_f  st) where
  micro (P_f p) = P_f (\k st -> microstep ( p k st ) )
-}

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% State Change          %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

class Switch p where
  pSwitch :: (st1 -> (st1',st2)) -> ((st1', st2) -> st1) -> p st2 a -> p st1 a

instance Switch P_h where
  pSwitch f g (P_h p) = P_h  (\ k h st1 ->  let (st1', st2) = f st1
                                            in p (\ h st2' -> k h (g (st1', st2'))) h st2
                             )

instance Switch P_f where
  pSwitch f g (P_f p) = P_f  (\k st1 ->  let (st1',st2) = f st1
                                         in p (\st2' -> k (g (st1', st2'))) st2
                             )

instance Switch P_m where
  pSwitch f g (P_m (p, q)) = P_m (pSwitch f g p, pSwitch f g q)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Recognisers           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

newtype  R st a  = R (forall r . (st -> Steps   r) -> st -> Steps r)
unR (R p) = p

instance Applicative (R st) where
 R p  <*>  R q   =   R (p . q)
 pure a       =   R (id)

instance Alternative (R st) where
 R p  <|>  R q   =   R (\ k inp  -> p k inp `best` q k inp)  
 empty           =   R (\ k inp  -> noAlts)
instance Functor (R st) where
    fmap f = (pure f <*>)

instance  (Show symbol, Describes symbol token, Provides state symbol token) =>  Symbol (R  state) symbol token where
  pSym a =  R (  let p = \ k inp ->  
                        let ins ex =  case insertSym a inp ex of
                                      Just  (c_i, v,  st_i) ->  Just  (c_i, (k st_i))
                                      Nothing               ->  Nothing
                            del s ss ex  =  case deleteTok a s ss inp ex of
                                            Just  (c_d, st_d) ->  Just (c_d,  p k  st_d)
                                            Nothing           ->  Nothing
                        in  case splitState a inp of
                            Just (s, ss, pr)   ->  if a `eqSymTok` s  
                                                   then  Step pr ((k ss)) 
                                                   else  Fail [show a] [ins, del s ss]                                              
                            -- Nothing       ->             Fail [show a] [ins]
                   in p)

class Applicative p => ExtApplicative p st where
  (<*)      ::  p  a          -> R st b   ->   p  a
  (*>)      ::  R  st b          -> p    a   ->   p  a
  (<$$)      ::  a            -> R st b   ->   p  a


instance ExtApplicative (P_h st ) st where
  P_h p <* R r     = P_h (\ k h st -> p (\ ha st -> r (k ha) st) h st)
  R   r *> P_h p   = P_h (\ k h st -> r (p k h) st)
  f     <$$  R r   = P_h (\ k h st -> r (k (h, f)) st)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Some Instances        %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


instance Eq a => Describes a a where
     eqSymTok  = (==)

data Error t s pos = Inserted s pos Strings
                   | Deleted  t pos Strings
                   | DeletedAtEnd t
                   deriving Show

data Str     t    = Str   {  input    :: [t]
                          ,  msgs     :: [Error t t Int ]
                          ,  pos      :: !Int
                          ,  deleteOk :: !Bool}

listToStr ls = Str   ls  []  0  True

instance Provides  (Str  a)  a  a where
       splitState a (Str  []       _    _    _    )        = Nothing
       splitState a (Str  (t:ts)   msgs pos  ok   )        = Just (t, Str ts msgs (pos + 1) True, 1)
       insertSym s (Str  i        msgs pos  ok   )   exp  
          = Just (5, s, Str i (msgs ++ [Inserted s pos exp]) pos False)
       deleteTok a i (Str  ii       _    pos  True ) 
                   (Str  _        msgs pos' True )   exp  
          = (Just (5,  Str ii (msgs ++ [Deleted i pos' exp]) pos True)) 
       deleteTok   _ _ _ _  _                                   
          = Nothing

instance Eof (Str a) where
       eof (Str  i        _    _    _    )        = null i
       deleteAtEnd (Str  (i:ii)   msgs pos ok    )        = Just (5, Str ii (msgs ++ [DeletedAtEnd i]) pos ok)
       deleteAtEnd _                                      = Nothing


instance  Stores (Str a) [Error a a Int] where
       getErrors   (Str  inp      msgs pos ok    )        = (msgs, Str inp [] pos ok)

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%% Simple test cases     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type P b =  P_m (Str Char) b -> String -> (b, [Error Char Char Int]) 
test :: P b
test p inp = parse ( (,) <$> p <*> pEnd) (listToStr inp)

lift a = [a]

pa, pb :: P_m (Str  Char) [Char] 
pa = lift <$> pSym 'a'
pb = lift <$> pSym 'b'
p <++> q = (++) <$> p <*> q
pa2 =   pa <++> pa
pa3 =   pa <++> pa2

pMany p = (\ a b -> b+1) <$> p <*> pMany p <<|> pure 0
pCount 0 p = pure []
pCount n p = (:) <$> p <*> pCount (n-1) p

main :: IO ()
main = do print (test pa "a")
          print (test pa "b")
          print (test pa2 "bbab")
          print (test pa "ba")
          print (test pa "aa")
          print (test  (do  l <- pMany pa
                            pCount l pb) "aaacabbb")
          print (test (amb ( (++) <$> pa2 <*> pa3 <|> (++) <$> pa3 <*> pa2))  "aaabaa")


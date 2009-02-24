\begin{code}
{-# LANGUAGE FlexibleInstances #-}

module Main where

import Code
import Example
import System.IO
import Control.Monad (when)
data State = State
    {
      lt, rt :: String,
      ls :: [Process Char Top]
    }


data Focus = L | M | R

cur M = "^"
cur _ = ""
      
showS focus _ (Atom c) = cur focus ++ [c]
showS focus _ Missing = cur focus ++ "*expected atom*"
showS focus _ (Deleted c) = cur focus ++ "?"++[c]++"?"
showS focus ([open,close]:ps) (S s@(BList l r) actualClose) = 
   case focus of 
       M -> open : mid ++ closing
       f -> open : concatMap (showS f ps) (toList s) ++ closing
    where
      closing = case actualClose of
         (Just ')') ->[close]
         (Just c) -> "?" ++ [c] ++ "?"
         Nothing -> "*expected )*"
      mid = concatMap (showS L ps) (l []) ++ case r of
          [] ->""
          [x] ->concatMap (showS R ps) r
          (a:x:rs) -> showS L ps a ++ showS M ps x ++ concatMap (showS R ps) rs

instance Show SExpr where
    show = showS M (cycle ["()","[]","{}"])
instance Show (BList SExpr) where
    show ss = showS M (cycle ["()","[]","{}"]) (S ss (Just ')')) 


loop s@State{ls = pst:psts } = do
  putStrLn ""
  putStrLn $ reverse (lt s) ++ "^" ++ rt s
  putStrLn $ show $ evalZR $ feedSyms Nothing $ feedSyms (Just (rt s)) $ pst 
  c <- getChar
  loop $ case c of
    '<'  -> case lt s of
              [] -> s
              (x:xs) -> s {lt = xs, rt = x : rt s, ls = psts}
    '>'  -> case rt s of
              [] -> s
              (x:xs) -> s {lt = x : lt s, rt = xs, ls = feed x}
    ','  -> case lt s of
              [] -> s
              (x:xs) -> s {lt = xs, ls = psts}
    '.'  -> case rt s of
              [] -> s
              (x:xs) -> s {rt = xs}
    c    -> s {lt = c : lt s, ls = feed c}
 where feed c = evalZL (feedSyms (Just [c]) pst) : ls s


main = hSetBuffering stdin NoBuffering >> loop State {lt = "", rt = "", ls = [mkProcess parseTopLevel]}
  


\end{code}
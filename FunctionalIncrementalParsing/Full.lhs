\begin{code}

module Main where

import Code
import Example
import System.IO
import Control.Monad (when)
data State = State
    {
      lt, rt :: String,
      ls :: [Process Char SExpr]
    }



      
showS _ (Atom c) = [c]
showS _ Missing = "*expected atom*"
showS _ (Deleted c) = "?"++[c]++"?"
showS ([open,close]:ps) (S s (Just ')')) = open : concatMap (showS ps) s ++ [close]
showS ([open,close]:ps) (S s Nothing) = open : concatMap (showS ps) s ++ "*expected )*"
showS ([open,close]:ps) (S s (Just c)) = open : concatMap (showS ps) s ++ "?" ++ [c] ++ "?"

instance Show SExpr where
    show = showS (cycle ["()","[]","{}"])


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
 where feed c = feedSyms (Just [c]) pst : ls s


main = hSetBuffering stdin NoBuffering >> loop State {lt = "", rt = "", ls = [mkProcess parseTopLevel]}
  


\end{code}
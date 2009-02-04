\section{Main loop}
Section \ref{sec:input} describes all the elements forming the interface of our final parsing library.

\begin{itemize}
 \item |Parser :: * -> * -> *|: The type of parser descriptions. Is is parametrized by token type and parsing result.
 \item |Zip :: * -> * -> *|: The type of parser states, parametrized as |Parser|.
 
 \item |mkProcess :: Parser s a -> Zip s a|: given a parser description, create the corresponding initial parsing state.
 \item |feedSyms :: Maybe [s] -> Zip s a -> Zip s a|: feed the parsing state with a number of symbols, or the end of input.
 \item |evalZL :: Zip s a -> Zip s a|: transform a parsing state by pre-computing all the intermediate parsing results available.
 \item |evalZR :: Zip s a -> a|: compute the final result of the parsing, in an online way. This assumes that the end of input has been fed into the process.
\end{itemize}

Using those we can write a toy editor with incremental parsing as follows:

\ignore{
\begin{code}
module Main where

import Code
import Example
import System.IO
import Control.Monad (when)
\end{code}
}

\begin{code}
data State a = State
    {
      lt, rt :: String,
      ls :: [Zip Char a]
    }

\end{code}
The |State| structure stores the ``current state'' of our toy editor. 
The fields |lt| and |rt| contain the text respectively to the left and to the right of the edit point.

The |ls| field is our main interest: it contains the parsing states corresponding to each symbol to the left of the edit point.

\begin{code}
loop :: Show a => State a -> IO b
loop s@State{ls = pst:psts } = do
  putStrLn ""
  putStrLn $ show 
           $ evalZR 
           $ feedSyms Nothing 
           $ feedSyms (Just (rt s)) 
           $ pst 
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
\end{code}

Note that the main loop is entirely generic over the type of the AST being produced.

Thus we can instanciate it, for example, with our parser for s-expressions, as follows.

\begin{code}
main = do  hSetBuffering stdin NoBuffering
           loop State {lt = "", 
                       rt = "", 
                       ls = [mkProcess parseTopLevel]}
\end{code}


The only missing piece is the |Show| instance for that type.
\begin{code}
showS _ (Atom c) = [c]
showS _ Missing = "*expected atom*"
showS _ (Deleted c) = "?"++[c]++"?"
showS ([open,close]:ps) (S s userClose)  =   open 
                                         :   concatMap (showS ps) s 
                                         ++  closing
    where closing = case userClose of 
             Just ')'  ->[close]
             Nothing   - "*expected )*"
             Just c    - "?" ++ [c] ++ "?"


instance Show SExpr where
    show = showS (cycle ["()","[]","{}"])

\end{code}




\textmeta{Remaining issues: focus, big jumps}
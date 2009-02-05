% -*- latex -*-
\section{Main loop}

This section identifies the elements of forming the interface of our final
parsing library, and shows how a toy application can be written using it.

Section \ref{sec:input} describes all the techniques needed to build these elements.

Parsing combinator libraries are usually composed of a parser type, and a |run| function
that executes the parser on a given input: |run :: Parser s a -> [s] -> [a]|.
Our system requires finer grainer execution of the parser. Therefore, we have to split the
|run| function into pieces and reify the parser state.
We propose the following types:

\begin{itemize}
 \item |Parser :: * -> * -> *|: The type of parser descriptions. Is is parametrized by token type and parsing result.
 \item |Process :: * -> * -> *|: The type of parser states, parametrized as |Parser|.
\end{itemize}

We also need a few functions to create and manipulate the parsing processes:

\begin{itemize}
 
 \item |mkProcess :: Parser s a -> Process s a|: given a parser description, create the corresponding initial parsing state.
 \item |feed :: [s] -> Process s a -> Process s a|: feed the parsing state with a number of symbols.
 \item |feedEof :: Process s a -> Process s a|: feed the parsing state with a number of symbols.
 \item |precompute :: Process s a -> Process s a|: transform a parsing state by pre-computing all the intermediate parsing results available.
 \item |finish :: Process s a -> a|: compute the final result of the parsing, in an online way. This assumes that the end of input has been fed into the process.
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


The |State| structure stores the ``current state'' of our toy editor. 
The fields |lt| and |rt| contain the text respectively to the left and to the right of the edit point.
The |ls| field is our main interest: it contains the parsing states corresponding to each symbol to the left of the edit point.
Note that there is always ore more element in |ls| than |lt|, because we also have a parser state for the empty input.

\begin{code}
data State a = State
    {
      lt, rt :: String,
      ls :: [Process Char a]
    }

\end{code}

The main loop of the editor naively written as follows. 
First, the current value of the document is being produced and displayed.
This means that we feed the remainder of the input to the current state and
run the parser. The display is trimmed to show only a window around the edition point.

Next, the user input is taken care of: movement, deletion and insertion of text are possible.
The main task is to keep the list of intermediate state synchronized with the
text. For example, every time a character is typed, a new parser state is
computed and stored. The other edition operations proceed in similar fashion.


\begin{code}
windowSize = 10

loop :: Show a => State a -> IO b
loop s@State{ls = pst:psts } = do
  putStrLn ""
  let windowBegin = length (lt s) - windowSize
  putStrLn $ take windowSize
           $ drop windowBegin
           $ show 
           $ finish
           $ feedEof
           $ feed (rt s)
           $ pst 
  c <- getChar
  loop $ case c of
    -- cursor movements
    '<'  -> case lt s of
              [] -> s
              (x:xs) -> s {lt = xs, rt = x : rt s, ls = psts}
    '>'  -> case rt s of
              [] -> s
              (x:xs) -> s {lt = x : lt s, rt = xs, ls = addState x}
    -- deletions
    ','  -> case lt s of
              [] -> s
              (x:xs) -> s {lt = xs, ls = psts}
    '.'  -> case rt s of
              [] -> s
              (x:xs) -> s {rt = xs}
    -- insertion of text
    c    -> s {lt = c : lt s, ls = addState c}
 where addState c = feed [c] pst : ls s
\end{code}


Note that the main loop is entirely independent of the type of the AST being produced.
Thus we can instanciate it, with any parser description, as follows:

\begin{code}
main = do  hSetBuffering stdin NoBuffering
           loop State {lt = "", 
                       rt = "", 
                       ls = [mkProcess parseTopLevel]}
\end{code}

This code illustrates the skeleton of any program using the library. A number
of issues are neglected though. Notably, we would like to avoid re-parsing when
moving in the file even if no modification is made. Also, the displayed output
will be computed from its start, and then trimmed. Instead we'd like to directly
print the portion corresponding to the current window. This issue can be tricky
to fix, but for the time being we will assume that displaying is much faster than
parsing and therefore can be neglected.


\ignore{
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
}


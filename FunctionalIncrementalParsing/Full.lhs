% -*- latex -*-


\ignore{
\begin{code}
module Main where

import Code
import Example
import System.IO
import Control.Monad (when)
\end{code}
}

\section{Main loop}
\label{sec:mainloop}
This section shows how to build identifies the elements of forming the interface of our final
parsing library, and shows how a toy application can be written using it.


On top of the interface decribed in section \ref{sec:interface}, we can write a toy editor with incremental parsing.

The main loop alternates beween displaying the contents of the file being
edited and updating its internal state in response to user input.

\begin{code}
loop :: Show a => State a -> IO ()
loop s = display s >> update s >>= loop
\end{code}

\begin{code}
data State a = State
    {
      lt, rt :: String,
      ls :: [Process Char a]
    }

\end{code}

The |State| structure stores the ``current state'' of our toy editor. 
The fields |lt| and |rt| contain the text respectively to the left and to the right of the edit point.
The |ls| field is our main interest: it contains the parsing processes corresponding to each symbol to the left of the edit point.
Note that there is always ore more element in |ls| than |lt|, because we also have a parser state for the empty input.


We do not display the input document as typed by the user, but an annotated version.
Therefore, we have to parse the input and then serialize the result.
First, we feed the remainder of the input to the current state and then
run the online parser. The display is then trimmed to show only a window around the edition point.

\begin{code}
display s =
  putStrLn ""
  let windowBegin = length (lt s) - windowSize
  putStrLn   $ take windowSize
             $ drop windowBegin
             $ show 
             $ finish
             $ feedEof
             $ feed (rt s)
             $ pst 
  where windowSize = 10 -- arbitrary value
\end{code}


There are three types of user input to take care of: movement, deletion and insertion of text.
The main difficulty here is to keep the list of intermediate states synchronized with the
text. For example, every time a character is typed, a new parser state is
computed and stored. The other edition operations proceed in similar fashion.

\begin{code}
update s@State{ls = pst:psts} = do
  c <- getChar
  return $ case c of
    -- cursor movements
    '<'  -> case lt s of -- left
              [] -> s
              (x:xs) -> s {lt = xs, rt = x : rt s, ls = psts}
    '>'  -> case rt s of -- right
              [] -> s
              (x:xs) -> s {lt = x : lt s, rt = xs, ls = addState x}
    -- deletions
    ','  -> case lt s of -- backspace
              [] -> s
              (x:xs) -> s {lt = xs, ls = psts}
    '.'  -> case rt s of -- delete
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
           loop State {
               lt = "", 
               rt = "", 
               ls = [mkProcess parseTopLevel]}
\end{code}

This code illustrates the skeleton of any program using our library. A number
of issues are glossed over though. Notably, we would like to avoid re-parsing when
moving in the file even if no modification is made. Also, the displayed output
will be computed from its start, and then trimmed. Instead we would like to directly
print the portion corresponding to the current window. This issue can be tricky
to fix, but for the time being we will assume that displaying is much faster than
parsing and therefore the running time of the former can be neglected.


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


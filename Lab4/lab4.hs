import System.Environment (getArgs)
import System.Exit (exitFailure)

import AbsHSK
import LexHSK
import ParHSK
import ErrM

import Interpreter

check :: String -> String -> IO ()
check str s = do
  case pProgram (myLexer s) of
    Bad err  -> do
      putStrLn "SYNTAX ERROR"
      putStrLn err
      exitFailure
    Ok  tree -> do
                case interpret tree str of
                  Bad err -> do putStrLn "INTERPRETATION ERROR"
                                putStrLn err
                                exitFailure
                  Ok res  -> putStrLn $ show res
                  

main :: IO ()
main = do
  args <- getArgs
  case args of
    []-> do
         putStrLn "Usage: lab2 <SourceFile>"
         exitFailure
    [str, file] -> readFile file >>= check str
    [file]      -> readFile file >>= check "-v"
    

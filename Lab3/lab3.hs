import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath.Posix (dropExtension,
                              takeFileName,
                              takeDirectory)
import System.Process (runCommand, waitForProcess)
    
import Prelude

import AbsCPP
import LexCPP
import ParCPP
import ErrM

import TypeChecker
import CodeGenerator


--------------------------------------------------------------------------------

        
main :: IO ()
main = do
  args <- getArgs
  case args of
    [file] -> do
              content <- readFile file
              let className = dropExtension $ takeFileName file
              let jFileName = dropExtension file ++ ".j"
              let dirName   = takeDirectory file
              code <- compile content className
              writeFile jFileName code
              putStrLn jFileName
              jasmin <- runCommand $ "java -jar jasmin.jar -d "
                   ++ dirName ++ " " ++ jFileName
              waitForProcess jasmin
              copy <- runCommand $ "cp runtime.class " ++ dirName
              waitForProcess copy
              return ()
    _      -> do
      putStrLn "Usage: lab2 <SourceFile>"
      exitFailure




compile :: String -> String -> IO String
compile s className = do
  case pProgram (myLexer s) of
    Bad err  -> do
      putStrLn "SYNTAX ERROR"
      putStrLn err
      exitFailure
    Ok tree -> do
      case typecheck tree of
        Bad err -> do
          putStrLn "TYPE ERROR"
          putStrLn err
          exitFailure
        Ok _ -> return $ generateCode tree className



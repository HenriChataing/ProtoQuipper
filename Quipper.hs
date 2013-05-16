module Main where

import Parser
import Lexer

import Classes

import Syntax
import Printer
import CoreSyntax
import TransCore

import qualified Interpret
import Values
import TypeInference
import CTypeInference

import System.IO
import System.Environment

data Options = Opt {
  inter :: Bool,
  typ :: Bool,
  printp :: Bool,
  filename :: String
}

initOptions = Opt {
  inter = False,
  typ = False,
  printp = False,
  filename = ""
}

options :: [(String, Options -> IO Options)]
options = [
  ("-i", (\opt -> return opt { inter = True })),
  ("-t", (\opt -> return opt { typ = True })),
  ("-p", (\opt -> return opt { printp = True })) ]

parseOptions :: [String] -> IO Options
parseOptions [] =
  return initOptions
parseOptions (s:cs) = do
  opt <- parseOptions cs
  case lookup s options of
    Just f -> f opt
    Nothing -> return opt { filename = s }

main = do
  -- Parse program options
  args <- getArgs
  opt <- parseOptions args

  -- Lex and parse file
  putStrLn $ "\x1b[1;34m" ++ "## Parsing content of file " ++ filename opt ++ "\x1b[0m"
  contents <- readFile $ filename opt
  prog <- return (parse $ mylex (filename opt) contents)

  -- Actions
  if printp opt then do
    putStrLn $ "\x1b[1;33m" ++ ">> Printing" ++ "\x1b[0m"
    putStrLn $ "\x1b[1m" ++ "Surface syntax :" ++ "\x1b[0m"
    putStrLn $ pprint prog
    putStrLn $ "\x1b[1m" ++ "Core syntax :" ++ "\x1b[0m"
    putStrLn (pshow $ fst $ translateExpr prog CTypeInference.newContext) 
  else
    return ()

  if inter opt then do
    putStrLn $ "\x1b[1;33m" ++ ">> Interpret" ++ "\x1b[0m" 
    case Interpret.run (dropConstraints prog) of
      Ok v -> do
          putStrLn $ show v
      Failed s ex -> do
          putStrLn $ "\x1b[1m" ++ "xx Interpretation failed xx" ++ "\x1b[0m"
          putStrLn ("In file : " ++ filename opt ++ ":" ++ show ex ++ " -- " ++ s)
  else
    return ()

  if typ opt then do
    putStrLn $ "\x1b[1;33m" ++ ">> Typing" ++ "\x1b[0m"
    putStrLn $ "\x1b[1m" ++ "TypeInference :" ++ "\x1b[0m"
    putStrLn (show $ TypeInference.principalType prog)
    putStrLn $ "\x1b[1m" ++ "CTypeInference :" ++ "\x1b[0m"
    putStrLn (show $ CTypeInference.principalType prog)
  else
    return ()
 

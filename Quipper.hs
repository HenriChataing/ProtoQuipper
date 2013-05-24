module Main where

import Parser
import Lexer

import Classes
import Utils

import Syntax
import Printer

import CoreSyntax
import TransSyntax
import TypingMain

import qualified Interpret
import Values

import System.IO
import System.Environment

data Options = Opt {
  inter :: Bool,
  typ :: Bool,
  printp :: Bool,
  test :: Bool,
  filename :: String
}

initOptions = Opt {
  inter = False,
  typ = False,
  printp = False,
  test = False,
  filename = ""
}

options :: [(String, Options -> IO Options)]
options = [
  ("-i", (\opt -> return opt { inter = True })),
  ("-t", (\opt -> return opt { typ = True })),
  ("-p", (\opt -> return opt { printp = True })),
  ("-test", (\opt -> return opt { test = True })) ]

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
    putStrLn $ pprint (clear_location prog)
    putStrLn $ "\x1b[1m" ++ "Core syntax :" ++ "\x1b[0m"
    putStrLn (pprint $ snd $ (let TransSyntax.State run = translateExpr (drop_constraints $ clear_location prog)  in run TransSyntax.empty_context)) 
  else
    return ()

  if inter opt then do
    putStrLn $ "\x1b[1;33m" ++ ">> Interpret" ++ "\x1b[0m" 
    case Interpret.run (drop_constraints prog) of
      Ok v -> do
          putStrLn $ pprint v
      Failed err -> do
          putStrLn $ "\x1b[1m" ++ "xx Interpretation failed xx" ++ "\x1b[0m"
          putStrLn $ show err
  else
    return ()

  if typ opt then do
    putStrLn $ "\x1b[1;33m" ++ ">> Typing" ++ "\x1b[0m"
    putStrLn $ "\x1b[1m" ++ "TypeInference :" ++ "\x1b[0m"
--    putStrLn $ pprint_constraints $ type_inference prog
    putStrLn $ full_inference prog
  else
    return ()

  if test opt then do
    putStrLn $ "\x1b[1;33m" ++ ">> Typing test" ++ "\x1b[0m"
    putStrLn $ "\x1b[1m" ++ "Test TypeInference :" ++ "\x1b[0m"
--    putStrLn $ pprint_constraints $ type_inference prog
    putStrLn $ test_full_inference 10
  else
    return ()
 

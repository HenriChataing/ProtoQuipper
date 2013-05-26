module Main where

import Parser
import Lexer

import Classes
import Utils
import Args

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
  -- Current options
  do_interpret :: Bool,
  do_typing :: Bool,
  do_printing :: Bool,
  do_testing :: Bool, testing_lvl :: Int,
  filename :: String
}

-- Some setters
set_interpret :: Options -> Options
set_typing :: Options -> Options
set_printing :: Options -> Options
set_testing :: Int -> Options -> Options
parse_file :: String -> Options -> Options
--------------------------------
set_interpret opt = opt { do_interpret = True }
set_typing opt = opt { do_typing = True }
set_printing opt = opt { do_printing = True }
set_testing n opt = opt { do_testing = True, testing_lvl = n }
parse_file f opt = opt { filename = f }

-- Intitial state
init_options = Opt {
  do_interpret = False,
  do_typing = False,
  do_printing = False,
  do_testing = False, testing_lvl = 0,
  filename = ""
}

-- Option continuations
option_defs :: ParseResult Options ()
option_defs = do
  when_parse "-i" (do apply set_interpret)
  when_parse "-t" (do apply set_typing)
  when_parse "-p" (do apply set_printing)
  when_parse "-test" (do
      s <- next
      n <- return (read s :: Int)
      apply $ set_testing n)
  when_default (\s -> do apply $ parse_file s)

-------------------------------------------------------------

main = do
  -- Parse program options
  args <- getArgs
  opt <- return $ run_parser init_options args option_defs

  -- Lex and parse file
  putStrLn $ "\x1b[1;34m" ++ "## Parsing content of file " ++ filename opt ++ "\x1b[0m"
  contents <- readFile $ filename opt
  prog <- return (parse $ mylex (filename opt) contents)

  -- Actions
  if do_printing opt then do
    putStrLn $ "\x1b[1;33m" ++ ">> Printing" ++ "\x1b[0m"
    putStrLn $ "\x1b[1m" ++ "Surface syntax :" ++ "\x1b[0m"
    putStrLn $ pprint (clear_location prog)
    putStrLn $ "\x1b[1m" ++ "Core syntax :" ++ "\x1b[0m"
    putStrLn (pprint $ snd $ (let TransSyntax.State run = translateExpr (drop_constraints $ clear_location prog)  in run TransSyntax.empty_context)) 
  else
    return ()

  if do_interpret opt then do
    putStrLn $ "\x1b[1;33m" ++ ">> Interpret" ++ "\x1b[0m" 
    case Interpret.run (drop_constraints prog) of
      Ok v -> do
          putStrLn $ pprint v
      Failed err -> do
          putStrLn $ "\x1b[1m" ++ "xx Interpretation failed xx" ++ "\x1b[0m"
          putStrLn $ show err
  else
    return ()

  if do_typing opt then do
    putStrLn $ "\x1b[1;33m" ++ ">> Typing" ++ "\x1b[0m"
    putStrLn $ "\x1b[1m" ++ "TypeInference :" ++ "\x1b[0m"
--    putStrLn $ pprint_constraints $ type_inference prog
    putStrLn $ full_inference prog
  else
    return ()

  if do_testing opt then do
    putStrLn $ "\x1b[1;33m" ++ ">> Typing test" ++ "\x1b[0m"
    putStrLn $ "\x1b[1m" ++ "Test TypeInference :" ++ "\x1b[0m"
--    putStrLn $ pprint_constraints $ type_inference prog
    putStrLn $ test_full_inference 10
  else
    return ()
 

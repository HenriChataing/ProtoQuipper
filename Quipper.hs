module Main where

import Parser
import ConstraintParser
import Lexer
import QuipperExport

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

-- Specification of the input parser
option_spec :: Options ()
option_spec = do
  -- Option init
  "do_interpret" <-- False
  "do_type" <-- False
  "do_print" <-- False
  "do_unify" <-- False
  "filename" <-- ""
  "unify" <-- ""
  -- Continuations
  when_parse "-i" (do "do_interpret" <-- True)
  when_parse "-t" (do "do_type" <-- True)
  when_parse "-p" (do "do_print" <-- True)
  when_parse "--unify" (do
      s <- next_arg
      "do_unify" <-- True
      "unify" <-- s)
  when_default (\s -> do "filename" <-- s)

-------------------------------------------------------------

main = do
  -- Parse program options
  args <- getArgs
  opt <- return $ run_parser args option_spec
  filename <- return $ ((value "filename" opt) :: String)

  -- Lex and parse file
  prog <- case value "filename" opt of
            "" -> do
                putStrLn "unspecified input file"
                return Syntax.EUnit
            _ -> do
                putStrLn $ "\x1b[1;34m" ++ "## Parsing content of file " ++ filename ++ "\x1b[0m"
                contents <- readFile filename
                return (parse $ mylex filename contents)

  -- Actions
  if value "do_print" opt then do
    putStrLn $ "\x1b[1;33m" ++ ">> Printing" ++ "\x1b[0m"
    putStrLn $ "\x1b[1m" ++ "Surface syntax :" ++ "\x1b[0m"
    putStrLn $ pprint (clear_location prog)
  else
    return ()

  if value "do_interpret" opt then do
    putStrLn $ "\x1b[1;33m" ++ ">> Interpret" ++ "\x1b[0m" 
    case Interpret.run (drop_constraints prog) of
      Ok v -> do
          putStrLn $ pprint v
      Failed err -> do
          putStrLn $ "\x1b[1m" ++ "xx Interpretation failed xx" ++ "\x1b[0m"
          putStrLn $ show err
  else
    return ()

  if value "do_type" opt then do
    putStrLn $ "\x1b[1;33m" ++ ">> Typing" ++ "\x1b[0m"
    putStrLn $ "\x1b[1m" ++ "TypeInference :" ++ "\x1b[0m"
    putStrLn $ full_inference prog
  else
    return ()

  if value "do_unify" opt then do
    putStrLn  $ "\x1b[1;33m" ++ ">> unification test" ++ "\x1b[0m"
    set <- return $ parse_constraints $ mylex "" $ value "unify" opt
    putStrLn $ test_unification set
  else
    return () 

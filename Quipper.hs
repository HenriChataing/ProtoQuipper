module Main where

import Parser
import ConstraintParser
import Lexer
import QuipperError
import qualified QpState as Q

import Classes
import Utils

import Syntax
import Printer

import CoreSyntax
import TransSyntax
import Driver

import qualified Interpret
import Values

import System.IO
import System.Environment
import System.Console.GetOpt
import qualified Control.Exception as E
import Options

import Data.List as List

----------------------------------------------

main = do
  -- Parse program options
  argv <- getArgs
  (opts, files) <- parseOpts argv

  -- Program actions
  if showHelp opts then
    putStrLn $ usageInfo header options
  else
    return ()

  if showVersion opts && not (showHelp opts) then
    putStrLn $ version
  else
    return ()

  if not (showVersion opts) && not (showHelp opts) then do
    -- Unify option
    case runUnify opts of
      Just set -> do
          putStrLn  $ "\x1b[1;33m" ++ ">> unification test" ++ "\x1b[0m"
          tokens <- mylex set
          constraints <- return $ parse_constraints tokens
          (do
             s <- unification_test constraints
             putStrLn s) `E.catch` (\(e :: QError) -> do
                                      putStrLn $ show e)

      Nothing -> do
          -- Other options
          if files == [] then do
            putStrLn "No argument file specified"
            putStrLn $ usageInfo header options
          else do
            -- For now, only the first file is kept and treated
            -- Read and parse the file

            file <- return $ List.head files
            putStrLn $ "\x1b[1;33m" ++ ">> Quipper" ++ "\x1b[0m"
            (do
               (_, (v, t)) <- Q.runS (do
                 Q.set_verbose (verbose opts)
                 do_everything opts file) Q.empty_context
               case v of
                 Just v -> putStrLn $ pprint v
                 Nothing -> return ()
               putStrLn $ pprint t) `E.catch` (\(e :: QError) -> putStrLn $ show e)
  else
    return ()


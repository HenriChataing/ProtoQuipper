{-# LANGUAGE ScopedTypeVariables #-}

-- | Main module, which contains the main function that patches everything together.
module Main where

import Parsing.Parser
import Parsing.ConstraintParser
import Parsing.Lexer

import Monad.QuipperError
import qualified Monad.QpState as Q

import Classes
import Utils

import Parsing.Syntax
import Parsing.Printer

import Typing.CoreSyntax
import Typing.TransSyntax
import Typing.Driver

import Interpret.Values
import Interpret.Interpret
import Interpret.IRExport

import System.IO
import System.Environment
import System.Console.GetOpt
import qualified Control.Exception as E
import Options

import Data.List as List

-- | Main function. Parses the command line arguments, and acts accordingly.
main :: IO ()
main = do
  -- Parse program options
  argv <- getArgs
  (opts, files) <- parseOpts argv

  -- Proto quipper
  case files of
    [] -> optFail "-: No argument file specified"
    [file] -> 
          (do
             (_, (v, t)) <- Q.runS (do
               Q.set_verbose (verbose opts)
               (v, t) <- do_everything opts file
               t <- Q.pprint_type_noref t
               return (v, t)) Q.empty_context
             case (v, circuitFormat opts) of
               (Just (VCirc _ c _), "ir") -> do
                 irdoc <- return $ export_to_IR c
                 putStrLn irdoc

               (Just (VCirc _ c _), "visual") -> do
                 putStrLn $ pprint c

               (Just v, _) -> putStrLn $ (pprint v ++ " : " ++ t)
               (Nothing, _) -> putStrLn $ "-: " ++ t) `E.catch` (\(e :: QError) -> putStrLn $ show e)

    _ -> optFail "-: Several input files"


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
import System.FilePath.Posix
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
    _ -> do
        -- Automatically include the directories of the files
        dirs <- return $ List.nub $ List.map (\f -> takeDirectory f ++ "/") files
        opts <- return $ opts { includes = List.union dirs (includes opts) }
        (do
           _ <- Q.runS (do
               Q.set_verbose (verbose opts)
               do_everything opts files) Q.empty_context
           return ()) `E.catch` (\(e :: QError) -> putStrLn $ show e)


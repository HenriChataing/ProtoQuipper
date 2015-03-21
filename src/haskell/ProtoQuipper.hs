{-# LANGUAGE ScopedTypeVariables #-}

-- | This is the main module of Proto-Quipper. It contains the 'main' function, which reads the command line arguments, and runs accordingly.
module Main where

import Monad.QuipperError
import qualified Monad.QpState as Q

import Core.Syntax

import Driver
import Builtins

import Core.Translate
import Core.Environment

import System.IO
import System.Environment
import System.Exit
import System.FilePath.Posix
import qualified Control.Exception as E
import Options

import Interactive

import Compiler.Circ

import qualified Data.Map as Map
import qualified Data.IntMap as IMap
import Data.List as List

-- | Main function. Parses the command line arguments. About the input files:
--
-- * If several are given, they are all executed successively (but not necessarily following the order in which they were
--   given as it may change depending on the dependencies).
--
-- * The directory of an input file is automatically added to the list of include directories.
--
-- * If no file is specified, Proto-Quipper switches to the interactive mode (see "Interactive").
main :: IO ()
main = do
  -- Parse program options
  argv <- getArgs
  (opts, files) <- parseOpts argv

  -- Proto quipper
  case files of
    [] -> do
        putStrLn "### Proto-Quipper -- Interactive Mode ###"
        _ <- Q.runS (do
            define_builtins
            lbl <- Q.global_namespace []
            run_interactive opts (Context { labelling = lbl,
                                            typing = IMap.empty,
                                            environment = IMap.empty, constraints = emptyset }) []
            return ()) Q.empty_context
        return ()

    _ -> do
        -- Automatically include the directories of the files
        dirs <- return $ List.nub $ List.map (\f -> takeDirectory f) files
        opts <- return $ opts { includes = List.union dirs (includes opts) }
        (do
           _ <- Q.runS (do
               Q.set_verbose (verbose opts)
               Q.set_warning_action (warning_action opts)
               do_everything opts files) Q.empty_context
           return ()) `E.catch` (\(e :: QuipperError) -> die e)
  where
    die e = do
      hPutStrLn stderr $ show e
      exitFailure
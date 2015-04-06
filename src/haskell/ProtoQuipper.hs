{-# LANGUAGE ScopedTypeVariables #-}

-- | This is the main module of Proto-Quipper. It contains the 'main' function, which reads the command
-- line arguments, and runs accordingly.
module Main where

import Driver
import Builtins
import Options

import Monad.Error
import Monad.Core as Core
import Monad.Typer as Typer

import Core.Syntax
import Core.Translate
import Core.Environment

import Interactive

import System.IO
import System.Environment
import System.Exit
import System.FilePath.Posix

import Data.List as List

import Control.Exception
import Control.Monad.Trans.State
import Control.Monad.Trans


-- | Main function. Parses the command line arguments. About the input files:
--
-- * If several are given, they are all executed successively (but not necessarily following the
--   order in which they were given as it may change depending on the dependencies).
--
-- * The directory of an input file is automatically added to the list of include directories.
--
-- * If no file is specified, Proto-Quipper switches to the interactive mode (see "Interactive").
--
main :: IO ()
main = do
  -- Parse program options.
  argv <- getArgs
  (opts, files) <- parseOpts argv

  -- Proto quipper.
  case files of
    [] -> do
      putStrLn "### Proto-Quipper -- Interactive Mode ###"
      let interactiveMode = do
            defineBuiltins
            changeOptions (\_ -> opts)
            launchInteractive
      (_, _) <- runStateT interactiveMode Core.init
      return ()

    _ -> do
      -- Automatically include the directories of the files.
      let dirs = List.nub $ (List.map takeDirectory files) ++ (includeDirs opts)
      let normalMode = do
            changeOptions (\_ -> opts { includeDirs = dirs })
            runStateT (processModules files) Typer.empty
      (do
          (_, _) <- runStateT normalMode Core.init
          return ()) `catch` (\(e :: SomeException) -> die e)

  where
    die e = do
      hPutStrLn stderr $ show e
      exitFailure

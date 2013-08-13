{-# LANGUAGE ScopedTypeVariables #-}

-- | Main module, which contains the main function that patches everything together.
module Main where

import Monad.QuipperError
import qualified Monad.QpState as Q

import Typing.CoreSyntax
import Typing.Driver
import Typing.TransSyntax

import System.IO
import System.Environment
import System.FilePath.Posix
import qualified Control.Exception as E
import Options

import Interactive

import qualified Data.Map as Map
import qualified Data.IntMap as IMap
import Data.List as List

-- | Main function. Parses the command line arguments, and acts accordingly.
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
            import_builtins
            run_interactive opts (Context { label = Map.empty, typing = IMap.empty,
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
               do_everything opts files) Q.empty_context
           return ()) `E.catch` (\(e :: QError) -> putStrLn $ show e)


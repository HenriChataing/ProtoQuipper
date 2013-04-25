module Main where

import Parser
import Lexer

import System.IO
import System.Environment
import System.Exit

data Options = Opt {
  interpret :: Bool,
  typing :: Bool,
  printp :: Bool,
  files :: [String]
}

initOptions = Opt {
  interpret = False,
  typing = False,
  printp = False,
  files = []
}

options :: [(String, Options -> IO Options)]
options = [
  ("-i", (\opt -> return opt { interpret = True })),
  ("-t", (\opt -> return opt { typing = True })),
  ("-p", (\opt -> return opt { printp = True })) ]

parseOptions :: [String] -> IO Options
parseOptions [] =
  return initOptions
parseOptions (s:cs) = do
  opt <- parseOptions cs
  case lookup s options of
    Just f -> f opt
    Nothing -> return opt { files = s:(files opt) }

main = do
  args <- getArgs
  opt <- parseOptions args
  inter <- return $ interpret opt
  typ <- return $ typing opt
  pr <- return $ printp opt
  putStrLn ("interpret=" ++ show inter)
  putStrLn ("typing=" ++ show typ)
  putStrLn ("printp=" ++ show pr)
  putStr "files="
  mapM putStrLn (files opt)
  

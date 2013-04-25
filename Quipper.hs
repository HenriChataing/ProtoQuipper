module Main where

import Parser
import ParserUtils
import Lexer
import Syntax

import System.IO
import System.Environment

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

  progs <- mapM (\f -> do
                    contents <- readFile f
                    return $ parse $ mylex contents) (files opt)

  if interpret opt then
    putStrLn "Interpret"
  else
    return ()

  if typing opt then
    putStrLn "Typing"
  else
    return ()

  if printp opt then
    mapM (\e -> do
                  putStrLn (show e)) progs
  else
    return [()]

  mapM putStrLn (files opt)
 

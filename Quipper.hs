module Main where

import Parser
import ParserUtils
import Lexer
import Syntax

import Interpret
import TypeInference

import System.IO
import System.Environment

data Options = Opt {
  inter :: Bool,
  typ :: Bool,
  printp :: Bool,
  files :: [String]
}

initOptions = Opt {
  inter = False,
  typ = False,
  printp = False,
  files = []
}

options :: [(String, Options -> IO Options)]
options = [
  ("-i", (\opt -> return opt { inter = True })),
  ("-t", (\opt -> return opt { typ = True })),
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

  if printp opt then
    mapM (\e -> do
                  putStrLn (show e)) progs
  else
    return [()]

  if inter opt then
    mapM (\e -> do
             putStrLn (let (v, ctx) = Interpret.run (dropConstraints e) Interpret.newContext in (show v))) progs
  else
    return [()]

  if typ opt then
    mapM (\e -> do
             putStrLn (show $ TypeInference.principalType e)) progs
  else
    return [()]
 

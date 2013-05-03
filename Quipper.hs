module Main where

import Parser
import Lexer
import Syntax
import Classes

import Interpret
import TypeInference

import System.IO
import System.Environment

data Options = Opt {
  inter :: Bool,
  typ :: Bool,
  printp :: Bool,
  filename :: String
}

initOptions = Opt {
  inter = False,
  typ = False,
  printp = False,
  filename = ""
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
    Nothing -> return opt { filename = s }

main = do
  -- Parse program options
  args <- getArgs
  opt <- parseOptions args

  -- Lex and parse file
  putStrLn ("## Parsing content of file " ++ (filename opt))
  contents <- readFile $ filename opt
  prog <- return (parse $ mylex (filename opt) contents)

  -- Actions
  if printp opt then do
    putStrLn (">> Typing")
    putStrLn (show prog)
    putStrLn ("<< Done")
  else
    return ()

  if inter opt then do
    putStrLn (">> Interpret")
    putStrLn (show $ Interpret.run (dropConstraints prog))
    putStrLn ("<< Done")
  else
    return ()

  if typ opt then
    putStrLn (show $ TypeInference.principalType prog)
  else
    return ()
 

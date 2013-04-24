module Main where

import Parser
import Lexer

import System.IO

main = do
  hSetBuffering stdin LineBuffering
  file <- getLine
  contents <- readFile file
  print $ parse $ alexScanTokens contents

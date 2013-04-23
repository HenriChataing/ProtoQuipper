module Main where

import Parser
import Lexer

import System.IO

main = do
  hSetBuffering stdin LineBuffering
  term <- getLine
  print $ parse $ lexer term

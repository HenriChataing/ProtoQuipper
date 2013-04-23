module ParserUtils where

import Data.Char
import Syntax

data ParseResult a = Ok a | Failed String
  deriving Show

type Locus = (Int, Int)
type P a = String -> Locus -> ParseResult a

getLocus :: P Locus
getLocus = \s l -> Ok l

thenP :: P a -> (a -> P b) -> P b
thenP m k = \s l ->
  case m s l of
    Ok a -> k a s l
    Failed e -> Failed e

returnP :: a -> P a
returnP a = \s l -> Ok a

failP :: String -> P a
failP e = \s l -> Failed e

catchP :: P a -> (String -> P a) -> P a
catchP m k = \s l ->
  case m s l of
    Ok a -> Ok a
    Failed e -> k e s l


  

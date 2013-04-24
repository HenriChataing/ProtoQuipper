module ParserUtils where

import Data.Char
import Syntax

data E a = Ok a | Failed String
  deriving Show

thenE :: E a -> (a -> E b) -> E b
thenE m k =
  case m of
    Ok a -> k a
    Failed e -> Failed e

returnE :: a -> E a
returnE a = Ok a

failE :: String -> E a
failE e = Failed e

catchE :: E a -> (String -> E a) -> E a
catchE m k =
  case m of
    Ok a -> Ok a
    Failed e -> k e


  

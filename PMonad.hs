module PMonad where

import Data.Char

data ParseResult a = Ok a | Failed String
  deriving Show

type Locus = (Int, Int)
type P a = String -> Locus -> ParseResult a

getLocus :: P Locus
getLocus = \s l -> Ok l

nextLine :: (Locus -> ParseResult a) -> (Locus -> ParseResult a)
nextLine m = \(l, c) -> m (l+1, c)

nextChar :: (Locus -> ParseResult a) -> (Locus -> ParseResult a)
nextChar m = \(l, c) -> m (l, c+1)

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


  

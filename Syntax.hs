module Syntax where

import Data.Char

data Kind =
    KUnit
  | KBool
  | KQBit
  | KCirc Kind Kind
  | KTensor Kind Kind
  | KArrow Kind Kind
  | KExp Kind
    deriving Show

data Pattern =
    PVar String
  | PPair Pattern Pattern
    deriving Show

data Term =
    TEmpty
  | TVar String
  | TFun [Pattern] Term
  | TLet Pattern Term Term
  | TApp Term Term
  | TTrue
  | TFalse
  | TPair Term Term
  | TBox Kind Term
  | TUnbox Term
  | TCirc Term Term Term
  | TIf Term Term Term
  | TRev Term
    deriving Show

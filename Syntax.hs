module Syntax where

import Data.Char

data Type =
    TUnit
  | TBool
  | TQBit
  | TCirc Type Type
  | TTensor Type Type
  | TArrow Type Type
  | TExp Type
    deriving Show

data Pattern =
    PVar String
  | PPair Pattern Pattern
    deriving Show

data Expr =
    EEmpty
  | EVar String
  | EFun [Pattern] Expr
  | ELet Pattern Expr Expr
  | EApp Expr Expr
  | ETrue
  | EFalse
  | EPair Expr Expr
  | EBox Type Expr
  | EUnbox Expr
  | ECirc Expr Expr Expr
  | EIf Expr Expr Expr
  | ERev Expr
    deriving Show

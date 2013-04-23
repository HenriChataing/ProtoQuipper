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
  | TLocated Type (Int, Int)
    deriving Show

data Pattern =
    PVar String
  | PPair Pattern Pattern
  | PLocated Pattern (Int, Int)
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
  | ELocated Expr (Int, Int)
    deriving Show

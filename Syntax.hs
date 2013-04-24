module Syntax where

import Data.Char
import Lexer

data Type =
    TUnit
  | TBool
  | TQBit
  | TCirc Type Type
  | TTensor Type Type
  | TArrow Type Type
  | TExp Type
  | TLocated Type Extent
    deriving Show

locate_type :: Extent -> Type -> Type
locate_type _ (TLocated t ex) = TLocated t ex
locate_type ex t = TLocated t ex

data Pattern =
    PVar String
  | PPair Pattern Pattern
  | PLocated Pattern Extent
    deriving Show

locate_pattern :: Extent -> Pattern -> Pattern
locate_pattern _ (PLocated p ex) = PLocated p ex
locate_pattern ex p = PLocated p ex

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
  | ELocated Expr Extent
    deriving Show

locate_expr :: Extent -> Expr -> Expr
locate_expr _ (ELocated e ex) = ELocated e ex
locate_expr ex e = ELocated e ex


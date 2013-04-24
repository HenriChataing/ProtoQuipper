module Syntax where

import Data.Char
import Lexer

class Located a where
  locate :: a -> Extent -> a
  locate_opt :: a -> Maybe Extent -> a
  location :: a -> Maybe Extent

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

instance Located Type where
  locate (TLocated t ex) _ = TLocated t ex
  locate t ex = TLocated t ex
  location (TLocated _ ex) = Just ex
  location _ = Nothing
  locate_opt t Nothing = t
  locate_opt t (Just ex) = locate t ex

data Pattern =
    PVar String
  | PPair Pattern Pattern
  | PLocated Pattern Extent
    deriving Show

instance Located Pattern where
  locate (PLocated p ex) _ = PLocated p ex
  locate p ex = PLocated p ex
  location (PLocated _ ex) = Just ex
  location _ = Nothing
  locate_opt p Nothing = p
  locate_opt p (Just ex) = locate p ex

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

instance Located Expr where
  locate (ELocated e ex) _ = ELocated e ex
  locate e ex = ELocated e ex
  location (ELocated _ ex) = Just ex
  location _ = Nothing
  locate_opt e Nothing = e
  locate_opt e (Just ex) = locate e ex


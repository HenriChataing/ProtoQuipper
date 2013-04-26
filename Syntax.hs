module Syntax where

import Data.Char
import Localizing

---------------------------------
-- Class of objects that can   --
-- be assorted with a location --

class Located a where
  locate :: a -> Extent -> a
  locateOpt :: a -> Maybe Extent -> a
  location :: a -> Maybe Extent

class Atomic a where
  isAtomic :: a -> Bool

---------------------------------
-- Representation of Quipper's --
-- types                       --

data Type =
    TUnit
  | TBool
  | TQBit
  | TCirc Type Type
  | TTensor Type Type
  | TArrow Type Type
  | TExp Type
  | TLocated Type Extent

instance Atomic Type where
  isAtomic (TTensor _ _) = False
  isAtomic (TArrow _ _) = False
  isAtomic (TLocated t _) = isAtomic t
  isAtomic _ = True

instance Located Type where
  locate (TLocated t ex) _ = TLocated t ex
  locate t ex = TLocated t ex
  location (TLocated _ ex) = Just ex
  location _ = Nothing
  locateOpt t Nothing = t
  locateOpt t (Just ex) = locate t ex

instance Show Type where
  show TUnit = "()"
  show TBool = "bool"
  show TQBit = "qbit"
  show (TCirc t1 t2) = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (TTensor t1 t2) =
    (if isAtomic t1 then show t1
     else "(" ++ show t1 ++ ")") ++ " * " ++
    (if isAtomic t2 then show t2
     else "(" ++ show t2 ++ ")")
  show (TLocated t _) = show t
  show (TExp t) = "!" ++ (if isAtomic t then show t else "(" ++ show t ++ ")")
  show (TArrow t1 t2) =
    (if isAtomic t1 then show t1
     else "(" ++ show t1 ++ ")") ++ " -> " ++
    (if isAtomic t2 then show t2
     else "(" ++ show t2 ++ ")")

---------------------------------
-- Representation of patterns  --
-- from let .. in expressions  --

data Pattern =
    PVar String
  | PPair Pattern Pattern
  | PLocated Pattern Extent

instance Located Pattern where
  locate (PLocated p ex) _ = PLocated p ex
  locate p ex = PLocated p ex
  location (PLocated _ ex) = Just ex
  location _ = Nothing
  locateOpt p Nothing = p
  locateOpt p (Just ex) = locate p ex

instance Show Pattern where
  show (PLocated p _) = show p
  show (PVar s) = s
  show (PPair p1 p2) = "<" ++ show p1 ++ ", " ++ show p2 ++ ">"

---------------------------------
-- Quipper's terms             --

data Expr =
    EEmpty
  | EVar String
  | EFun Pattern Expr
  | ELet Pattern Expr Expr
  | EApp Expr Expr
  | EBool Bool
  | EPair Expr Expr
  | EBox Type
  | EUnbox Expr
  | ECirc Expr Expr Expr
  | EIf Expr Expr Expr
  | ERev
  | ELocated Expr Extent

instance Located Expr where
  locate (ELocated e ex) _ = ELocated e ex
  locate e ex = ELocated e ex
  location (ELocated _ ex) = Just ex
  location _ = Nothing
  locateOpt e Nothing = e
  locateOpt e (Just ex) = locate e ex

instance Atomic Expr where
  isAtomic (ELocated e _) = isAtomic e
  isAtomic (EApp _ _) = False
  isAtomic (EIf _ _ _) = False
  isAtomic (EFun _ _) = False
  isAtomic _ = True

instance Show Expr where
  show (ELocated e _) = show e
  show EEmpty = "()"
  show (EVar s) = s
  show (ELet p e1 e2) = "let " ++ show p ++ " = " ++ show e1 ++ " in\n " ++ show e2
  show (EBool b)  = if b then "true" else "false"
  show (EPair e1 e2) = "<" ++ show e1 ++ ", " ++ show e2 ++ ">"
  show (EIf e1 e2 e3) = "if " ++ show e1 ++ " then\n " ++ show e2 ++ "\n else\n " ++ show e3
  show (EApp e1 e2) =
    (if isAtomic e1 then show e1
     else "(" ++ show e1 ++ ")") ++ " " ++
    (if isAtomic e2 then show e2
     else "(" ++ show e2 ++ ")")
  show (EUnbox e) = if isAtomic e then "unbox " ++ show e else "unbox (" ++ show e ++ ")"
  show ERev = "rev"
  show (EBox t) = "box[" ++ show t ++ "]"
  show (EFun p e) = "fun " ++ (show p) ++ " -> " ++ (show e)
  

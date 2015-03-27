-- | Contains the definition of language data constructors.
module Language.Constructor where

import Utils

import Core.Syntax
import Compiler.SimplSyntax as C


-- | Information relative to a data constructor.
data ConstructorInfo = ConstructorInfo {
  name :: String,
  sourceModule :: String,           -- ^ Source module (empty if not relevant).
  sourceType :: Int,                -- ^ Associated type.
  typ :: TypeScheme,                -- ^ Type of the constructor.
  implementation :: Variable,       -- ^ Variable of the function that implements the constructor.
  tag :: Int,                       -- ^ Unique tag attributed to the constructor.
  build :: Either C.Expr (C.Expr -> C.Expr),   -- ^ Builder (compiler specific).
  extract :: Variable -> C.Expr                -- ^ Value extraction (compiler specific).
}

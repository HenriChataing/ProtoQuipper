-- | Contains the definition of language data constructors.
module Language.Type where

import Utils

import Core.Syntax


-- | Information relative to a type constructor.
data TypeInfo = TypeInfo {
  name :: String,
  sourceModule :: String,         -- ^ Source module (empty if not relevant).
  definition :: TypeDefinition,   -- ^ The original type definition (as written in the source).
  tag :: Int                      -- ^ For the compilation : indicates the location of the tag.
}

-- | Contains the definition of language data constructors.
module Language.Type where

import Utils

import Core.Syntax
import qualified Compiler.SimplSyntax as C (Expr)

-- ----------------------------------------------------------------------
-- ** Data type definitions


-- | Describe the variability of an argument.
data Variance =
    Unrelated         -- ^ No clue.
  | Covariant         -- ^ The argument is covariant.
  | Contravariant     -- ^ The argument is contravariant.
  | Equal             -- ^ The argument is both covariant and contravariant.
  deriving Eq


instance Show Variance where
  show Unrelated = ""
  show Equal = "="
  show Covariant = "+"
  show Contravariant = "-"


-- | Return the least precise indication of the two arguments.
join :: Variance -> Variance -> Variance
join Unrelated v = v
join v Unrelated = v
join Covariant Covariant = Covariant
join Contravariant Contravariant = Contravariant
join _ _ = Equal


-- Return the opposite variance.
opposite :: Variance -> Variance
opposite Covariant = Contravariant
opposite Contravariant = Covariant
opposite var = var


-- | A generic type definition.
data TypeDefinition =
    Algebraic {
      duplicable :: Bool,          -- ^ The data is always duplicable (e.g. circ, int ..) ?
      arguments :: [(Type, Variance)],
      constructors :: [(Datacon, Maybe Type)]
    }
  | Synonym {
      arguments :: [(Type, Variance)],
      duplicable :: Bool,          -- ^ The data is always duplicable (e.g. circ, int ..) ?
      alias :: Type
    }


-- | Information relative to a type constructor.
data TypeInfo = TypeInfo {
  name :: String,
  sourceModule :: String,         -- ^ Source module (empty if not relevant).
  definition :: TypeDefinition,   -- ^ The original type definition (as written in the source).
  tag :: Variable -> C.Expr       -- ^ For the compilation : indicates the location of the tag.
}

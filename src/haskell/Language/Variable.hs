-- | Contains the definition of language variables.
module Language.Variable where

import Core.Syntax


-- | Information relative to a variable.
data VariableInfo = VariableInfo {
  name :: String,
  sourceModule :: String,        -- ^ Source module (empty if not relevant).
  callingConvention :: [Type]    -- ^ Calling convention (set at unbox overloading).
}

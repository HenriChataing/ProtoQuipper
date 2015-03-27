-- | Contains the definition of language variables.
module Language.Variable where


-- | Information relative to a variable.
data VariableInfo = VariableInfo {
  name :: String,
  sourceModule :: String          -- ^ Source module (empty if not relevant).
}

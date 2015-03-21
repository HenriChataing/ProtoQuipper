-- | This module contains the definition of labelling contexts, used to respesent the scope of variables,
-- data constructors and types.
module Core.Environment where

import Classes
--import Utils

import Core.Syntax

import Data.Map (Map)
import qualified Data.Map as Map


-- ----------------------------------------------------------------------
-- * Labelling context.


-- | The type of variables in a labelling context; these can be either
-- local or global.
data Variable ident =
    Local ident     -- ^ Local variable: /x/.
  | Global ident    -- ^ Global variable from the imported modules.
  deriving (Show)


-- | Environment, corresponding to the variables available at one scope of the program.
data Environment ident = Environment {
  variables :: Map String (Variable ident),
  datacons :: Map String ident,
  types :: Map String Type
}


-- | Empty environment.
empty :: Environment ident
empty = Environment {
  variables = Map.empty,
  datacons = Map.empty,
  types = Map.empty
}


instance Context (Environment ident) where
  lbl <+> lbl' = Environment {
    variables = Map.union (variables lbl) (variables lbl'),
    datacons = Map.union (datacons lbl) (datacons lbl'),
    types = Map.union (types lbl) (types lbl')
  }

  lbl \\ lbl' = Environment {
    variables = variables lbl Map.\\ variables lbl',
    datacons = datacons lbl Map.\\ datacons lbl',
    types = types lbl Map.\\ types lbl'
  }


-- | Transform any local variable into a global one.
lvar_to_lglobal :: Environment ident -> Environment ident
lvar_to_lglobal environment = environment {
  variables = Map.map (\l -> case l of
      Local x -> Global x
      _ -> l
    ) $ variables environment
}

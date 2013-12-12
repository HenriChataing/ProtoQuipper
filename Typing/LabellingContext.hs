-- | This module gives the definition of a labelling context, used to represent
-- the variables, data constructors and type names currently in scope.
module Typing.LabellingContext where

import Classes
import Utils

import Core.Syntax

import Data.Map (Map)
import qualified Data.Map as Map


-- ----------------------------------------------------------------------
-- * Labelling context


-- | The type of variables in a labelling context; these can be either
-- local or global.
data LVariable =
    LVar Variable       -- ^ Variable: /x/.
  | LGlobal Variable    -- ^ Global variable from the imported modules.



-- | Labelling context: it contains the variable identifiers of all the variables, data constructors,
-- types in scope.
data LabellingContext = LblCtx {
  variables :: Map String LVariable,
  datacons :: Map String Datacon,
  types :: Map String Type
}


-- | Empty labelling map.
empty_label :: LabellingContext
empty_label = LblCtx {
  variables = Map.empty,
  datacons = Map.empty,
  types = Map.empty
}


instance Context LabellingContext where
  lbl <+> lbl' = LblCtx {
      variables = Map.union (variables lbl) (variables lbl'),
      datacons = Map.union (datacons lbl) (datacons lbl'),
      types = Map.union (types lbl) (types lbl')
    }

  lbl \\ lbl' = LblCtx {
      variables = variables lbl Map.\\ variables lbl',
      datacons = datacons lbl Map.\\ datacons lbl',
      types = types lbl Map.\\ types lbl'
    }


-- | Transform any local variable into a global one.
lvar_to_lglobal :: LabellingContext -> LabellingContext
lvar_to_lglobal lctx =
  lctx { variables = Map.map (\l -> case l of
        LVar x -> LGlobal x
        _ -> l) $ variables lctx }

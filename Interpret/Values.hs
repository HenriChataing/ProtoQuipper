-- | This module gives the definition of the type of values, used by the interpreter to represent
-- values (...). The definition follows from the definition of expression, but for a few differences
-- which are :
--    The application, if then else, match with, have all been eliminated, with the exception of unboxed circuits.
--    The function values include a closure in their definition, corresponding to the evaluation context at the time
--      of the evaluation of the function.
--    The qbits, which weren't included in the input syntax, are added, same for circuits.
module Interpret.Values where

import Classes
import Utils

import Typing.CoreSyntax
import Typing.CorePrinter

import Interpret.Circuits

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import qualified Data.List as List


-- | Definition of the type of values.
data Value =
    VFun (IntMap Value) Pattern Expr     -- ^ fun p -> e (in the context env).
  | VBuiltin (Value -> Value)            -- ^ builtin function.
  | VTuple [Value]                       -- ^ (v1, .. , vn)
  | VCirc Value Circuit Value            -- ^ (t, c, u)
  | VSumCirc Value                       -- ^ When the type of a circuit uses user types, a general specimen can't be inferred. A new circuit is produced for
                                         -- all new uses of the box.
  | VBool Bool                           -- ^ true / false
  | VInt Int                             -- ^ integer
  | VBox Type                            -- ^ box [T]
  | VUnbox                               -- ^ unbox
  | VUnboxed Value                       -- ^ unbox (t, c, u)
  | VUnit                                -- ^ ()
  | VDatacon Datacon (Maybe Value)       -- ^ datacon e
  | VRev                                 -- ^ rev
  | VQbit Int                            -- ^ Quantum addresses.


instance PPrint Value where
  pprint VUnit = "()"
  pprint VRev = "rev"
  pprint VUnbox = "unbox"
  pprint (VBuiltin _) = "<fun>"
  pprint (VQbit q) = subvar 'q' q
  pprint (VBool b) = if b then "true" else "false"
  pprint (VInt n) = show n
  pprint (VTuple (v:rest)) = "(" ++ pprint v ++ List.foldl (\s w -> s ++ ", " ++ pprint w) "" rest ++ ")"
  pprint (VCirc _ c _) = pprint c
  pprint (VSumCirc _) = "<circ>"
  pprint (VFun _ _ _) = "<fun>"
  pprint (VDatacon datacon e) =
    subvar 'D' datacon ++
      case e of
        Just e -> " " ++ pprint e
        Nothing -> ""
  pprint (VUnboxed _) = "<fun>"

  sprint v = pprint v
  sprintn _ v = pprint v
  genprint _ v _ = pprint v


-- | The equality between values is only about the skeleton. It is only to be used to compare quantum values, and
-- quantum addresses are ignored.
instance Eq Value where
  (==) (VQbit _) (VQbit _) = True
  (==) VUnit VUnit = True
  (==) (VTuple vlist) (VTuple vlist') =
    if List.length vlist == List.length vlist' then
      List.and $ List.map (\(v, v') -> v == v') (List.zip vlist vlist')
    else
      False
  (==) (VDatacon dcon v) (VDatacon dcon' v') = (dcon == dcon') && (v == v')


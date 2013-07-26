-- | This module gives the definition of the type of values, used by the interpreter to represent
-- values (...). The definition follows from the definition of expression, but for a few differences
-- which are :
--    The application, if then else, match with, have all been eliminated, with the exception of unboxed circuits
--    The function values include a closure in their definition, corresponding to the evaluation context at the time
--      of the evaluation of the function
--    The qbits, which weren't included in the input syntax, are added, same for circuits

module Values where

import Classes
import Utils

import CoreSyntax
import CorePrinter

import Circuits

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import qualified Data.List as List


-- | Type declaration of values
data Value =
    VFun (IntMap Value) Pattern Expr     -- fun p -> e (in the context env)
  | VTuple [Value]                       -- <v1, .. , vn>
  | VCirc Value Circuit Value            -- (t, c, u)
  | VBool Bool                           -- true / false
  | VBox Type                            -- box [T]
  | VUnbox                               -- unbox
  | VUnboxed Value                       -- unbox (t, c, u)
  | VUnit                                -- <>
  | VDatacon Datacon (Maybe Value)       -- datacon e
  | VRev                                 -- rev
  | VQbit Int                            -- Quantum addresses
  deriving Show


-- | Values are declared instances of PPrint
instance PPrint Value where
  pprint VUnit = "<>"
  pprint VRev = "rev"
  pprint VUnbox = "unbox"
  pprint (VQbit q) = subvar 'q' q
  pprint (VBool b) = if b then "true" else "false"
  pprint (VTuple (v:rest)) = "<" ++ pprint v ++ List.foldl (\s w -> s ++ ", " ++ pprint w) "" rest ++ ">"
  pprint (VCirc _ c _) = pprint c
  pprint (VFun _ p e) = "fun " ++ pprint p ++ " -> " ++ pprint e
  pprint (VDatacon datacon e) = subvar 'D' datacon ++ case e of
                                                        Just e -> "(" ++ pprint e ++ ")"
                                                        Nothing -> ""
  pprint (VUnboxed c) = "unbox (" ++ pprint c ++ ")"

  sprint v = pprint v
  sprintn _ v = pprint v



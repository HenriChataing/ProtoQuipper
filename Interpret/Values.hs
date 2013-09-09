-- | This module defines the type of values, used by the interpreter to represent
-- Proto-Quipper values. The definition is similar to that of expressions, except for a few differences,
-- which are:
-- 
-- *   Applications, if-then-else, and match-with have been dropped, with the exception of unboxed circuits.
-- 
-- *   The function values include a closure in their definition, corresponding to the evaluation context at the time
--    of the evaluation of the function.
-- 
-- *   Qubits and circuits, which were not included in the input syntax, are added.
module Interpret.Values where

import Classes
import Utils
import Monad.QuipperError

import Typing.CoreSyntax
import Typing.CorePrinter

import Interpret.Circuits

import Control.Exception
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import qualified Data.List as List


-- | The type of values.
data Value =
    VFun (IntMap Value) Pattern Expr     -- ^ @fun p -> e@ (in the given context).
  | VBuiltin (Value -> Value)            -- ^ Built-in function: these are defined as functions on 'Interpret.Values.Value', but not in terms of
                                         -- values.
  | VTuple [Value]                       -- ^ (v1, .. , vn)
  | VCirc Value Circuit Value            -- ^ (t, c, u)
  | VSumCirc Value                       -- ^ When the type of a circuit uses user types, a general specimen can't be inferred. A new circuit is produced for
                                         -- all new uses of the box.
  | VBool Bool                           -- ^ True and false.
  | VInt Int                             -- ^ Integers.
  | VBox Type                            -- ^ @box [T]@
  | VUnbox                               -- ^ @Unbox@.
  | VUnboxed Value                       -- ^ Unboxed circuits (can't be reduced any further). Note that the type of the value is not checked
                                         -- until application of the unboxed circuit.
  | VUnit                                -- ^ @()@
  | VDatacon Datacon (Maybe Value)       -- ^ @Datacon v@
  | VRev                                 -- ^ Reverse function.
  | VQubit Int                            -- ^ Quantum addresses.


instance PPrint Value where
  genprint l VUnit opts = "()"
  genprint l VRev opts = "rev"
  genprint l VUnbox opts = "unbox"
  genprint l (VBuiltin _) opts = "<fun>"
  genprint l (VQubit q) opts = subvar 'q' q
  genprint l (VBool b) opts = if b then "true" else "false"
  genprint l (VInt n) opts = show n
  genprint l (VTuple (v:rest)) opts = "(" ++ genprint l v opts ++ List.foldl (\s w -> s ++ ", " ++ genprint l w opts) "" rest ++ ")"
  genprint l (VTuple []) opts = 
    throw $ ProgramError "Value:genprint: illegal tuple"
  genprint l (VCirc _ c _) opts = pprint c
  genprint l (VSumCirc _) opts = "<circ>"
  genprint l (VFun _ _ _) opts = "<fun>"
  genprint l (VDatacon datacon e) [f] =
    case (f datacon, e) of
      -- List constructors
      ("Nil", Nothing) ->
          "[]"
      ("Cons", Just (VTuple [a, b])) ->
          let pa = genprint l a [f] in
          case genprint l b [f] of
            "[]" -> "[" ++ pa ++ "]"
            '[':rest -> "[" ++ pa ++ ", " ++ rest
            nope -> "Cons " ++ "(" ++ pa ++ "," ++ nope ++ ")"

      -- Others
      _ ->
        f datacon ++ case e of
                       Just e -> " " ++ genprint l e [f]
                       Nothing -> ""
  genprint l (VDatacon datacon e) opts =
    throw $ ProgramError "Value:genprint: illegal argument"
  genprint l (VUnboxed _) opts = "<fun>"
  genprint l (VBox t) opts = "<fun>"

  sprint v = pprint v
  sprintn _ v = pprint v
  pprint v = genprint Inf v [(subvar 'D')]


-- | Equality between values is only about the skeleton. It is only to be used to compare quantum values, and
-- quantum addresses are ignored.
instance Eq Value where
  (==) (VQubit _) (VQubit _) = True
  (==) VUnit VUnit = True
  (==) (VTuple vlist) (VTuple vlist') =
    if List.length vlist == List.length vlist' then
      List.and $ List.map (\(v, v') -> v == v') (List.zip vlist vlist')
    else
      False
  (==) (VDatacon dcon v) (VDatacon dcon' v') = (dcon == dcon') && (v == v')
  (==) _ _ = throw $ ProgramError "Value:==: illegal argument"

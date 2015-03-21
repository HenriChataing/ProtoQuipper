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

import Core.Syntax
import Core.Printer

import Interpret.Circuits

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
  genprint _ _ VUnit = "()"
  genprint _ _ VRev = "rev"
  genprint _ _ VUnbox = "unbox"
  genprint _ _ (VBuiltin _) = "<fun>"
  genprint _ _ (VQubit q) = prevar "q" q
  genprint _ _ (VBool b)  = if b then "true" else "false"
  genprint _ _ (VUnboxed _) = "<fun>"
  genprint _ _ (VBox t) = "<fun>"
  genprint _ _ (VInt n) = show n
  genprint _ _ (VFun _ _ _) = "<fun>"
  genprint _ _ (VCirc _ c _) = pprint c

  genprint (Nth 0) _ _ = "..."

  genprint lvl opts (VTuple (v:rest)) =
    let dlv = decr lvl in
    "(" ++ genprint dlv opts v ++ List.foldl (\s w -> s ++ ", " ++ genprint dlv opts w) "" rest ++ ")"
  genprint lvl [fdata] (VDatacon datacon e) =
    let dlv = decr lvl in
    case (fdata datacon, e) of
      -- List constructors
      ("_Nil", Nothing) ->
          "[]"
      ("_Cons", Just (VTuple [a, b])) ->
          let pa = genprint dlv [fdata] a in
          case genprint dlv [fdata] b of
            "[]" -> "[" ++ pa ++ "]"
            '[':rest -> "[" ++ pa ++ ", " ++ rest
            nope -> "Cons " ++ "(" ++ pa ++ "," ++ nope ++ ")"

      -- Others
      _ ->
        fdata datacon ++ case e of
                       Just e -> " " ++ genprint dlv [fdata] e
                       Nothing -> ""
  genprint l opts (VDatacon datacon e) =
    throwNE $ ProgramError "Values:genprint: illegal argument"
  genprint _ _ (VTuple []) =
    throwNE $ ProgramError "Values:genprint: illegal tuple"

  sprintn lvl v = genprint lvl [(prevar "D")] v


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
  (==) _ _ = throwNE $ ProgramError "Values:==: illegal argument"



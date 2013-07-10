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
import QpState

import CoreSyntax
import TransSyntax

import Circuits
import Gates

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
  | VInjL Value                          -- injl e
  | VInjR Value                          -- injr e
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
  pprint (VInjL e) = "injl(" ++ pprint e ++ ")"
  pprint (VInjR e) = "injr(" ++ pprint e ++ ")"
  pprint (VUnboxed c) = "unbox (" ++ pprint c ++ ")"

  sprint v = pprint v
  sprintn _ v = pprint v


-- | Creation of the gates
-- The gates are only listed by name in the Gates module, so a value need to be created for
-- each one. Note that the gates should already have been labeled (given a unique id) during
-- the syntax translation. The assiocations will be made with those ids, rather than the gates string names

gate_values :: QpState [(Int, Value)]
gate_values = do
  -- Creation of the init gates
  linit0 <- find_name "INIT0"
  linit1 <- find_name "INIT1"
  init_values <- return [(linit0, VCirc VUnit (Circ { qIn = [], gates = [ Init 0 0 ], qOut = [0] }) (VQbit 0)),
                         (linit1, VCirc VUnit (Circ { qIn = [], gates = [ Init 0 1 ], qOut = [0] }) (VQbit 0)) ]

  -- Creation of the term gates
  lterm0 <- find_name "TERM0"
  lterm1 <- find_name "TERM1"
  term_values <- return [(lterm0, VCirc (VQbit 0) (Circ { qIn = [], gates = [ Term 0 0 ], qOut = [0] }) VUnit),
                         (lterm1, VCirc (VQbit 0) (Circ { qIn = [], gates = [ Term 0 1 ], qOut = [0] }) VUnit) ]

  -- Creation of the unary gates
  unary_values <- List.foldl (\rec s -> do
                                r <- rec
                                lbl <- find_name s
                                g <- return (lbl, VCirc (VQbit 0) (Circ { qIn = [0], gates = [ Unary s 0 ], qOut = [0] }) (VQbit 0))
                                return (g:r)) (return []) unary_gates

  -- Creation of the binary gates
  binary_values <- List.foldl (\rec s -> do
                                 r <- rec
                                 lbl <- find_name s
                                 g <- return (lbl, VCirc (VTuple [VQbit 0, VQbit 1])
                                                         (Circ { qIn = [0, 1], gates = [ Binary s 0 1 ], qOut = [0, 1] })
                                                         (VTuple [VQbit 0, VQbit 1]))
                                 return (g:r)) (return []) binary_gates

  -- Return the whole
  return $ init_values ++ term_values ++ unary_values ++ binary_values


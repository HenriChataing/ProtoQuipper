-- | This module defines the interfaces of the modules Builtins and QLib that are assumed to be externally
-- defined.
module Compiler.Interfaces where

import Utils
import Classes
import Builtins

import Monad.QpState

import Interpret.Circuits

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List


class Interface a where
  lookup :: String -> a -> Maybe Variable     -- ^ Lookup a variable in the interface file.



-- | Interface of the Qlib module.
-- The builtin operations OPENBOX, CLOSEBOX, REV, UNENCAP (along with the builtin gates) all refer the global variables of some qlib module,
-- of which the implementation may vary. This structure enacts the qlib module by registrating the listed variables.
data IQLib = IQLib {
  iqlib :: Map String Variable               -- ^ The list of builtin gates and circuit constructors.
}


-- | Build the quantum interface from the list of builtin operations.
build_iqlib :: QpState IQLib
build_iqlib = do
  let ugates = List.map fst unary_gates
      bgates = List.map fst binary_gates
      qinit = ["INIT0", "INIT1"]
      qterm = ["TERM0", "TERM1"]
      others = ["OPENBOX", "CLOSEBOX", "REV", "UNENCAP"]  
  
  qlib <- List.foldl (\rec g -> do
        qi <- rec
        i <- register_var g 0
        return $ Map.insert g i qi) (return Map.empty) (ugates ++ bgates ++ qinit ++ qterm ++ others)

  return IQLib { iqlib = qlib }


instance Interface IQLib where
  lookup x qlib =
    Map.lookup x $ iqlib qlib



-- | Interface of the Builtins module.
-- The builtin operations OPENBOX, CLOSEBOX, REV, UNENCAP (along with the builtin gates) all refer the global variables of some qlib module,
-- of which the implementation may vary. This structure enacts the qlib module by registrating the listed variables.
data IBuiltins = IBuiltins {
  ibuiltins :: Map String Variable          -- ^ The list of builtin operations.
}


-- | Build the interface of the Builtins module.
build_ibuiltins :: QpState IBuiltins
build_ibuiltins = do
  let bops = Map.keys builtin_operations
  builtins <- List.foldl (\rec b -> do
        bi <- rec
        i <- register_var b 0
        return $ Map.insert b i bi) (return Map.empty) bops 

  return IBuiltins { ibuiltins = builtins }


instance Interface IBuiltins where
  lookup x builtins =
    Map.lookup x $ ibuiltins builtins




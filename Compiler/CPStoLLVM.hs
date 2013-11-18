-- | This module contains the functions necessary for the production of LLVM code.
module Compiler.CPStoLLVM where

import Utils

import Compiler.CPS

import Monad.QpState

import LLVM.Core as L

import Data.Int (Int32)


convert_to_llvm :: CExpr -> QpState (CodeGenFunction Int32 Terminate)
convert_to_llvm (CFun _ _ _ _) =
  fail "CPStoLLVM:convert_to_llvm: illegal argument"

convert_to_llvm (CApp f args) =
  return (do
        ret (value zero :: L.Value Int32)
      )
 
convert_to_llvm (CTuple vlist x c) = do
  c <- convert_to_llvm c
  
  return (do  
        c
      )

convert_to_llvm (CAccess n x y c) = do
  return (do
        ret (value zero :: L.Value Int32)
      )

convert_to_llvm (CSwitch v clist) = do
  return (do
        ret (value zero :: L.Value Int32)
      )


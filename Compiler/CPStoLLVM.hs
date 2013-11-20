{-# LANGUAGE CPP #-}

-- | This module contains the functions necessary for the production of LLVM code.
module Compiler.CPStoLLVM where

import Utils
import Classes

import Compiler.CPS as CPS

import Monad.QpState
import Monad.QuipperError

import LLVM.Core as L

import Data.Int (Int32, Int64)
import Data.Word (Word32, Word64)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import qualified Data.List as List


-- Type of integers (related to the architecture).
#if i386_HOST_ARCH
#define ArchInt Int32
#elif x86_64_HOST_ARCH
#define ArchInt Int64
#else
#error cannot determine type of archint
#endif


-- | The context of values build up during the transformation.
type LContext = IntMap (L.Value ArchInt)


-- | Convert a CPS value to the corresponding LLVM value. If the value is a variable, then
-- it goes through the map, else it returns an integer.
lvalue :: LContext -> CPS.Value -> L.Value ArchInt
lvalue _ (VInt n) =
  valueOf $ fromIntegral n
lvalue vals v =
  let fv = free_var v in
  case IMap.lookup (List.head fv) vals of
    Just v -> v
    Nothing -> throwNE $ ProgramError "CPStiLLVM:vlookup: undefined variable"


-- | Convert a CPS expression to LLVM code.
convert_to_llvm :: LContext                                      -- ^ Context of values.
                -> CExpr                                         -- ^ Continuation expression.
                -> CodeGenFunction ArchInt Terminate             -- ^ The result is a chunk of function code.
convert_to_llvm _ (CFun _ _ _ _) =
  fail "CPStoLLVM:convert_to_llvm: illegal argument"

convert_to_llvm vals (CApp f args) = do
  let vf = lvalue vals f
      vargs = List.map (lvalue vals) args
  -- build the function application
  -- this suppose functions do not take more than 3 arguments (function closure, actual argument, continuation)
  app <- case vargs of
        [a] -> do
            f <- bitcast vf :: CodeGenFunction r (L.Value (Ptr (ArchInt -> IO ArchInt)))
            call f a
        [a,b] -> do
            f <- bitcast vf :: CodeGenFunction r (L.Value (Ptr (ArchInt -> ArchInt -> IO ArchInt)))
            call f a b
        [a,b,c] -> do
            f <- bitcast vf :: CodeGenFunction r (L.Value (Ptr (ArchInt -> ArchInt -> ArchInt -> IO ArchInt)))
            call f a b c
        _ ->
            throwNE $ ProgramError "CPStoLLVM:convert_to_llvm: bad function application"
  -- the return value is that of the function application
  ret app
 
convert_to_llvm vals (CTuple vlist x c) = do
  -- allocate space for the tuple
  ptr <- arrayMalloc (fromIntegral $ List.length vlist :: Word32) :: CodeGenFunction r (L.Value (Ptr ArchInt))
  -- store the values into the array
  List.foldl (\rec (n,v) -> do
      rec
      ptrn <- getElementPtr ptr (fromIntegral n :: ArchInt, ())
      store v ptrn) (return ()) $ List.zip [0..List.length vlist -1] (List.map (lvalue vals) vlist)

  -- translate the continuation
  vx <- bitcast ptr :: CodeGenFunction r (L.Value ArchInt)
  convert_to_llvm (IMap.insert x vx vals) c

convert_to_llvm vals (CAccess n x y c) = do
  -- retrieve the array from the context
  let vx = lvalue vals x
  ptr <- bitcast vx
  -- access the nth element of the array
  ptrn <- getElementPtr ptr (fromIntegral n :: Int32, ())
  vy <- load ptrn
  -- translate the continuation
  convert_to_llvm (IMap.insert y vy vals) c

convert_to_llvm vals (CSwitch x clist) = do
  -- translate the value v, and check that it is indeed an integer
  let vx = lvalue vals x
  -- build the switch cases
  cases <- List.foldl (\rec c -> do
        blocks <- rec
        block <- createBasicBlock
        convert_to_llvm vals c
        return $ block:blocks) (return []) clist
  let tags = List.map (constOf . fromIntegral) [0..List.length clist - 2]    -- the last case is omited for it will be the default jump target
  
  let (bcases, dcase) = (List.init cases, List.last cases) 

  switch vx dcase $ List.zip tags bcases


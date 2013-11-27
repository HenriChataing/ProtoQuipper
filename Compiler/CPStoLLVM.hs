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


-- | The type of used llvm values.
data LValue =
    LVInt (L.Value ArchInt)                                               -- ^ Basic integers.
  | LVIntPtr (L.Value (Ptr ArchInt))                                      -- ^ Pointers.
  | LVFun2 (L.Function (ArchInt -> ArchInt -> IO ArchInt))                -- ^ Function taking two arguments.
  | LVFun3 (L.Function (ArchInt -> ArchInt -> ArchInt -> IO ArchInt))     -- ^ Function taking three arguments.


-- | The context of values build up during the transformation.
type LContext = IntMap LValue


-- | Proceed to the declaration of the imported functions.
declare_imported :: [CPS.Value] -> QpState (CodeGenModule LContext)
declare_imported [] =
  return $ return IMap.empty
declare_imported ((VLabel ix):ixs) = do
  nix <- variable_name ix
  m <- declare_imported ixs
  return (do
        vals <- m
        fix <- newNamedFunction ExternalLinkage nix :: CodeGenModule (Function (ArchInt -> ArchInt -> ArchInt -> IO ArchInt))
        return $ IMap.insert ix (LVFun3 fix) vals)
declare_imported ((VGlobal ix):ixs) = do
  nix <- variable_name ix
  m <- declare_imported ixs
  return (do
        vals <- m
        fix <- newNamedFunction ExternalLinkage nix :: CodeGenModule (Function (ArchInt -> ArchInt -> IO ArchInt))
        return $ IMap.insert ix (LVFun2 fix) vals)
declare_imported _ =
  fail "CPStoLLVM:declare_imported: illegal argument"


-- | Proceed to the declaration of the global variables.
declare_globals :: [Variable] -> CodeGenModule LContext
declare_globals [] =
  return IMap.empty
declare_globals (gx:gxs) = do
  vals <- declare_globals gxs
  ngx <- createGlobal False InternalLinkage (constOf 0) :: TGlobal ArchInt
  return $ IMap.insert gx (LVIntPtr ngx) vals


-- | Proceed to the declaration of the module fucntions.
declare_module_functions :: [(Variable, [Variable], CExpr)] -> QpState (CodeGenModule LContext)
declare_module_functions [] =
  return $ return IMap.empty
declare_module_functions ((f, [_,_], _):fs) = do
  nf <- variable_name f
  vals <- declare_module_functions fs
  return (do
        vf <- newNamedFunction ExternalLinkage nf :: CodeGenModule (Function (ArchInt -> ArchInt -> IO ArchInt))
        m <- vals
        return $ IMap.insert f (LVFun2 vf) m
      )
declare_module_functions ((f, [_,_,_], _):fs) = do
  nf <- variable_name f
  vals <- declare_module_functions fs
  return (do
        vf <- newNamedFunction ExternalLinkage nf :: CodeGenModule (Function (ArchInt -> ArchInt -> ArchInt -> IO ArchInt))
        m <- vals
        return $ IMap.insert f (LVFun3 vf) m
      )
declare_module_functions _ = do
  fail "CPStpLLVM:declare_module_functions: illegal argument"


-- | Proceed to the definition of the module functions.
define_module_functions :: LContext -> [(Variable, [Variable], CExpr)] -> CodeGenModule ()
define_module_functions _ [] =
  return ()
define_module_functions vals ((f, arg, c):fs) = do
  case (IMap.lookup f vals, arg) of
    (Just (LVFun2 f), [x,y]) -> do
        defineFunction f $ \vx vy -> do
              let vals' = IMap.insert x (LVInt vx) vals
              cexpr_to_llvm (IMap.insert y (LVInt vy) vals') c 
        define_module_functions vals fs 
    (Just (LVFun3 f), [x,y,z]) -> do
        defineFunction f $ \vx vy vz -> do
              let vals' = IMap.insert x (LVInt vx) vals
              let vals'' = IMap.insert y (LVInt vy) vals'
              cexpr_to_llvm (IMap.insert z (LVInt vz) vals'') c  
        define_module_functions vals fs 
    _ ->
        throwNE $ ProgramError "CPStoLLVM:define_module_functions: illegal argument"


-- | Convert a CPS value to an LLVM integer, using bitcast as needed.
lvalue_to_int :: LContext -> CPS.Value -> CodeGenFunction r (L.Value ArchInt)
lvalue_to_int _ (VInt n) =
  return $ valueOf $ fromIntegral n
lvalue_to_int vals v =
  let fv = free_var v in
  case IMap.lookup (List.head fv) vals of
    Just (LVInt v) -> return v
    Just (LVIntPtr p) -> load p
    Just (LVFun2 f) -> bitcast f
    Just (LVFun3 f) -> bitcast f
    Nothing -> throwNE $ ProgramError "CPStoLLVM:vlookup: undefined variable"


-- | Convert a CPS expression to LLVM code.
cexpr_to_llvm :: LContext                                      -- ^ Context of values.
                -> CExpr                                         -- ^ Continuation expression.
                -> CodeGenFunction ArchInt Terminate             -- ^ The result is a chunk of function code.
cexpr_to_llvm _ (CFun _ _ _ _) =
  fail "CPStoLLVM:cexpr_to_llvm: illegal argument"

cexpr_to_llvm vals (CApp f args) = do
  vf <- lvalue_to_int vals f
  vargs <- List.foldr (\a rec -> do
        as <- rec
        a <- lvalue_to_int vals a
        return $ a:as) (return []) args

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
            throwNE $ ProgramError "CPStoLLVM:cexpr_to_llvm: bad function application"
  -- the return value is that of the function application
  ret app
 
cexpr_to_llvm vals (CTuple vlist x c) = do
  -- allocate space for the tuple
  ptr <- arrayMalloc (fromIntegral $ List.length vlist :: Word32) :: CodeGenFunction r (L.Value (Ptr ArchInt))
  -- convert the values
  vlist <- List.foldr (\a rec -> do
        as <- rec
        a <- lvalue_to_int vals a
        return $ a:as) (return []) vlist
  -- store the values into the array
  List.foldl (\rec (n,v) -> do
      rec
      ptrn <- getElementPtr ptr (fromIntegral n :: ArchInt, ())
      store v ptrn) (return ()) $ List.zip [0..List.length vlist -1] vlist 

  -- translate the continuation
  vx <- bitcast ptr :: CodeGenFunction r (L.Value ArchInt)
  cexpr_to_llvm (IMap.insert x (LVInt vx) vals) c

cexpr_to_llvm vals (CAccess n x y c) = do
  -- retrieve the array from the context
  vx <- lvalue_to_int vals x
  ptr <- bitcast vx
  -- access the nth element of the array
  ptrn <- getElementPtr ptr (fromIntegral n :: Int32, ())
  vy <- load ptrn
  -- translate the continuation
  cexpr_to_llvm (IMap.insert y (LVInt vy) vals) c

cexpr_to_llvm vals (CSwitch x clist) = do
  -- translate the value v, and check that it is indeed an integer
  vx <- lvalue_to_int vals x
  -- build the switch cases
  cases <- List.foldl (\rec c -> do
        blocks <- rec
        block <- createBasicBlock
        cexpr_to_llvm vals c
        return $ block:blocks) (return []) clist
  let tags = List.map (constOf . fromIntegral) [0..List.length clist - 2]    -- the last case is omited for it will be the default jump target
  
  let (bcases, dcase) = (List.init cases, List.last cases) 

  switch vx dcase $ List.zip tags bcases

cexpr_to_llvm vals (CSet x v) = do
  vx <- lvalue_to_int vals (VVar x)
  vv <- lvalue_to_int vals v
  vx <- bitcast vx :: CodeGenFunction r (L.Value (Ptr ArchInt))
  store vv vx



-- | Convert a whole compilation unit to llvm.
cunit_to_llvm :: CUnit -> QpState (CodeGenModule ())
cunit_to_llvm cu = do
  -- declare the global variables
  gvals <- return $ declare_globals (List.map fst $ vglobals cu)
  -- declare the imported functions
  ivals <- declare_imported (imports cu)
  -- declare the functions
  fvals <- declare_module_functions (functions cu)
 
  return $ do
        gvals <- gvals
        ivals <- ivals
        fvals <- fvals
        let vals = IMap.union gvals $ IMap.union fvals ivals
        define_module_functions vals (functions cu)

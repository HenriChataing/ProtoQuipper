{-# LANGUAGE CPP #-}

-- | This module contains the functions necessary for the production of LLVM code.
module Compiler.LlvmExport where

import Utils
import Classes

import Compiler.CExpr as C

import Monad.QpState
import Monad.QuipperError

import LLVM.Core as L

import Data.Int (Int32, Int64)
import Data.Word (Word32, Word64)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import qualified Data.List as List
import System.IO (hFlush, stdout)

import Debug.Trace

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
  | LVExtern String                                                       -- ^ An imported variable or function, by its name.


-- | The context of values build up during the transformation.
type LContext = IntMap LValue


-- | Proceed to the declaration of the global variables.
declare_globals :: [Variable] -> QpState (CodeGenModule LContext)
declare_globals [] =
  return $ return IMap.empty
declare_globals (gx:gxs) = do
  name <- variable_name gx
  mod <- variable_module gx
  vals <- declare_globals gxs
  return $ do
        ngx <- createNamedGlobal False ExternalLinkage ("_" ++ mod ++ "_" ++ name) (constOf 0) :: TGlobal ArchInt
        vals <- vals
        return $ IMap.insert gx (LVIntPtr ngx) vals


-- | Proceed to the declaration of the module fucntions.
declare_module_functions :: Linkage -> [(Variable, [Variable], CExpr)] -> QpState (CodeGenModule LContext)
declare_module_functions linkage [] =
  return $ return IMap.empty
declare_module_functions ExternalLinkage ((f, arg, _):fs) = do
  nf <- variable_name f
  mod <- variable_module f
  vals <- declare_module_functions ExternalLinkage fs
  let fname = "_" ++ mod ++ "_" ++ nf
  case arg of
    [_,_] ->
        return (do
          vf <- newNamedFunction ExternalLinkage fname :: CodeGenModule (Function (ArchInt -> ArchInt -> IO ArchInt))
          m <- vals
          return $ IMap.insert f (LVFun2 vf) m
        )
    [_,_,_] ->
        return (do
          vf <- newNamedFunction ExternalLinkage fname :: CodeGenModule (Function (ArchInt -> ArchInt -> ArchInt -> IO ArchInt))
          m <- vals
          return $ IMap.insert f (LVFun3 vf) m
        )
    _ -> fail "LlvmExport:declare_module_functions: illegal argument"
declare_module_functions _ ((f, arg, _):fs) = do
  nf <- variable_name f
  vals <- declare_module_functions InternalLinkage fs
  case arg of
    [_,_] ->
        return (do
          vf <- newFunction InternalLinkage :: CodeGenModule (Function (ArchInt -> ArchInt -> IO ArchInt))
          m <- vals
          return $ IMap.insert f (LVFun2 vf) m
        )
    [_,_,_] ->
        return (do
          vf <- newFunction InternalLinkage :: CodeGenModule (Function (ArchInt -> ArchInt -> ArchInt -> IO ArchInt))
          m <- vals
          return $ IMap.insert f (LVFun3 vf) m
        )
    _ -> fail "LlvmExport:declare_module_functions: illegal argument"


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



-- | Convert a LLVM boxed value to an integer.
lvalue_to_int :: LValue -> CodeGenFunction r (L.Value ArchInt)
lvalue_to_int (LVInt v) = return v
lvalue_to_int (LVIntPtr p) = ptrtoint p
lvalue_to_int (LVFun2 f) = ptrtoint f
lvalue_to_int (LVFun3 f) = ptrtoint f
lvalue_to_int _ = throwNE $ ProgramError "CPStoLLVM:lvalue_to_int: illegal argument"


-- | Convert a CPS value to an LLVM integer, using casts as needed.
cvalue_to_int :: LContext -> C.Value -> CodeGenFunction r (L.Value ArchInt)
cvalue_to_int _ (VInt n) =
  return $ valueOf $ fromIntegral n
cvalue_to_int vals (VLabel l) =
  case IMap.lookup l vals of
    Just (LVExtern s) -> do
        p <- externFunction s :: CodeGenFunction r (Function (ArchInt -> ArchInt -> ArchInt -> IO ArchInt))
        ptrtoint p
    Just v -> lvalue_to_int v
    Nothing -> throwNE $ ProgramError $ "CPStoLLVM:cvalue_to_int: undefined label"
cvalue_to_int vals (VGlobal g) =
  case IMap.lookup g vals of
    Just (LVExtern s) -> do
        p <- externGlobal False s :: CodeGenFunction r (L.Value (Ptr ArchInt))
        ptrtoint p
    Just v -> lvalue_to_int v
    Nothing -> throwNE $ ProgramError $ "CPStoLLVM:cvalue_to_int: undefined global"
cvalue_to_int vals (VVar x) =
  case IMap.lookup x vals of
    Just v -> lvalue_to_int v
    Nothing -> throwNE $ ProgramError $ "CPStoLLVM:cvalue_to_int: undefined variable"



-- | Convert a CPS expression to LLVM code.
cexpr_to_llvm :: LContext                                      -- ^ Context of values.
                -> CExpr                                         -- ^ Continuation expression.
                -> CodeGenFunction ArchInt Terminate             -- ^ The result is a chunk of function code.
cexpr_to_llvm _ (CFun _ _ _ _) =
  fail "CPStoLLVM:cexpr_to_llvm: illegal argument"

cexpr_to_llvm vals (CApp f args x c) = do
  vf <- cvalue_to_int  vals f
  vargs <- List.foldr (\a rec -> do
        as <- rec
        a <- cvalue_to_int  vals a
        return $ a:as) (return []) args

  -- build the function application
  -- this suppose functions do not take more than 3 arguments (function closure, actual argument, continuation)
  app <- case vargs of
        [a] -> do
            f <- inttoptr vf :: CodeGenFunction r (L.Value (Ptr (ArchInt -> IO ArchInt)))
            call f a
        [a,b] -> do
            f <- inttoptr vf :: CodeGenFunction r (L.Value (Ptr (ArchInt -> ArchInt -> IO ArchInt)))
            call f a b
        [a,b,c] -> do
            f <- inttoptr vf :: CodeGenFunction r (L.Value (Ptr (ArchInt -> ArchInt -> ArchInt -> IO ArchInt)))
            call f a b c
        _ ->
            throwNE $ ProgramError "AlttoLLVM:alt_to_llvm: bad function application"
  -- the return value is that of the function application
  cexpr_to_llvm (IMap.insert x (LVInt app) vals) c

cexpr_to_llvm vals (CTailApp f args) = do
  vf <- cvalue_to_int  vals f
  vargs <- List.foldr (\a rec -> do
        as <- rec
        a <- cvalue_to_int  vals a
        return $ a:as) (return []) args

  -- build the function application
  -- this suppose functions do not take more than 3 arguments (function closure, actual argument, continuation)
  app <- case vargs of
        [a] -> do
            f <- inttoptr vf :: CodeGenFunction r (L.Value (Ptr (ArchInt -> IO ArchInt)))
            call f a
        [a,b] -> do
            f <- inttoptr vf :: CodeGenFunction r (L.Value (Ptr (ArchInt -> ArchInt -> IO ArchInt)))
            call f a b
        [a,b,c] -> do
            f <- inttoptr vf :: CodeGenFunction r (L.Value (Ptr (ArchInt -> ArchInt -> ArchInt -> IO ArchInt)))
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
        a <- cvalue_to_int vals a
        return $ a:as) (return []) vlist
  -- store the values into the array
  List.foldl (\rec (n,v) -> do
      rec
      ptrn <- getElementPtr ptr (fromIntegral n :: ArchInt, ())
      store v ptrn) (return ()) $ List.zip [0..List.length vlist -1] vlist

  -- translate the continuation
  vx <- ptrtoint ptr :: CodeGenFunction r (L.Value ArchInt)
  cexpr_to_llvm (IMap.insert x (LVInt vx) vals) c

cexpr_to_llvm vals (CAccess n x y c) = do
  -- retrieve the array from the context
  vx <- cvalue_to_int  vals x
  ptr <- inttoptr vx :: CodeGenFunction r (L.Value (Ptr ArchInt))
  -- access the nth element of the array
  ptrn <- getElementPtr ptr (fromIntegral n :: ArchInt, ())
  vy <- load ptrn
  -- translate the continuation
  cexpr_to_llvm (IMap.insert y (LVInt vy) vals) c

cexpr_to_llvm vals (CSwitch x clist def) = do
  -- translate the value v, and check that it is indeed an integer
  vx <- cvalue_to_int  vals x
  -- Build the switch cases.
  cases <- List.foldl (\rec (n, c) -> do
        let tag = constOf $ fromIntegral n
        blocks <- rec
        block <- createBasicBlock
        cexpr_to_llvm vals c
        return $ (tag, block):blocks) (return []) clist
  -- Build he default block.
  bdef <- createBasicBlock
  cexpr_to_llvm vals def

  -- Build the final expression.
  switch vx bdef cases

cexpr_to_llvm vals (CSet x v) = do
  vx <- cvalue_to_int  vals (VVar x)
  vv <- cvalue_to_int  vals v
  vx <- inttoptr vx
  store vv vx

cexpr_to_llvm vals (CRet v) = do
  vv <- cvalue_to_int  vals v
  ret vv

cexpr_to_llvm _ (CError msg) = do
  ret (fromIntegral 0 :: ArchInt)



-- | Convert a whole compilation unit to llvm.
cunit_to_llvm :: String -> CUnit -> QpState ()
cunit_to_llvm mods cu = do

  liftIO $ initializeNativeTarget
  mod <- liftIO $ newNamedModule mods

  -- declare the imported variables
  ivals <- List.foldl (\rec v -> do
        vals <- rec
        case v of
          VGlobal x -> do
              n <- variable_name x
              mod <- variable_module x
              return $ IMap.insert x (LVExtern $ "_" ++ mod ++ "_" ++ n) vals
          VLabel x -> do
              n <- variable_name x
              mod <- variable_module x
              return $ IMap.insert x (LVExtern $ "_" ++ mod ++ "_" ++ n) vals
          _ -> return vals) (return IMap.empty) (imports cu)

  -- declare the global variables
  gvals <- declare_globals (List.map fst $ vglobals cu)
  -- declare the functions
  efvals <- declare_module_functions ExternalLinkage (extern cu)
  lfvals <- declare_module_functions InternalLinkage (local cu)

  liftIO $ defineModule mod $ do
        gvals <- gvals
        efvals <- efvals
        lfvals <- lfvals
        let vals = IMap.union (IMap.union gvals ivals) (IMap.union lfvals efvals)
        -- define the functions
        define_module_functions vals (extern cu ++ local cu)
        -- define the module initializer
        initm <- createNamedFunction ExternalLinkage ("init" ++ mods) $
              List.foldr (\(_,cinit) rec -> do
                    cexpr_to_llvm vals cinit
                    rec
                  ) (ret $ valueOf (fromIntegral 0 :: Int64)) (vglobals cu) :: CodeGenModule (Function (IO ArchInt))
        -- Define the main function, if need be.
        case main cu of
          Just body -> do
              main <- createNamedFunction ExternalLinkage "main" $ do
                    _ <- call initm
                    cexpr_to_llvm vals body
              let _ = main :: Function (IO ArchInt)
              return ()
          Nothing ->
              return ()

  liftIO $ writeBitcodeToFile (mods ++ ".bc") mod



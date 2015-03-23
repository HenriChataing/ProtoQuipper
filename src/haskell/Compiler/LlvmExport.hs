{-# LANGUAGE CPP, ScopedTypeVariables, ExistentialQuantification #-}

-- | This module contains the functions necessary for the production of LLVM code.
module Compiler.LlvmExport where

import Utils
import Classes

import Compiler.CExpr as C

--import Monad.QpState
import Monad.Error

import LLVM.General.AST as A
import LLVM.General.AST.Global hiding (callingConvention, returnAttributes, functionAttributes)
import qualified LLVM.General.AST.Global as G
import LLVM.General.AST.Constant (Constant(Int, GlobalReference), integerBits, integerValue)
import LLVM.General.AST.CallingConvention
import LLVM.General.AST.Linkage
import LLVM.General.AST.AddrSpace
import LLVM.General.PrettyPrint
import LLVM.General.Module
import LLVM.General.Context

import Data.Int (Int32, Int64)
import Data.Word (Word8, Word32, Word64)
import Data.Bits (bitSize, Bits)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import qualified Data.List as List
import Data.ByteString (writeFile)
import System.IO hiding (writeFile)

import Control.Monad.Trans.Except


-- Type of integers (related to the architecture).
#if i386_HOST_ARCH
#define ArchInt Int32
#elif x86_64_HOST_ARCH
#define ArchInt Int64
#else
#error cannot determine type of archint
#endif



-- | Malloc function.
malloc :: Int -> String -> QpState (Named Instruction)
malloc n s =
  return $ Name s := Call {
    isTailCall = False,
    callingConvention = C,
    returnAttributes = [],
    function = Right $ ConstantOperand $ GlobalReference VoidType $ Name "malloc",
    arguments = [(ConstantOperand $ make_int (n * bitSize (0 :: ArchInt) `quot` 8), [])],
    functionAttributes = [],
    metadata = []
  }

-- | Create a Call instruction.
call :: Bool -> CallableOperand -> [Operand] -> Instruction
call tail func arg =
  Call {
    isTailCall = tail,
    callingConvention = C,
    returnAttributes = [],
    function = func,
    arguments = List.map (\a -> (a,[])) arg,
    functionAttributes = [],
    metadata = []
  }

-- | Cast an operand of some type into another.
cast :: Operand -> Typ -> Typ -> QpState (Operand, [Named Instruction])
cast op TyInt TyPtr = do
  tmp <- create_var "tmp"
  let nop = LocalReference int_type $ UnName $ fromIntegral tmp
  return (nop, [UnName (fromIntegral tmp) := IntToPtr op ptr_type []])
cast op TyInt (TyFun arg) = do
  tmp <- create_var "tmp"
  let nop = LocalReference int_type $ UnName $ fromIntegral tmp
  return (nop, [UnName (fromIntegral tmp) := IntToPtr op (PointerType (fun_type arg) (AddrSpace 0)) []])
cast op TyPtr TyInt = do
  tmp <- create_var "tmp"
  let nop = LocalReference VoidType $ UnName $ fromIntegral tmp
  return (nop, [UnName (fromIntegral tmp) := PtrToInt op int_type []])
cast op (TyFun _) TyInt = do
  tmp <- create_var "tmp"
  let nop = LocalReference VoidType $ UnName $ fromIntegral tmp
  return (nop, [UnName (fromIntegral tmp) := PtrToInt op int_type []])
cast op ty ty' | ty == ty' = return (op, [])
               | otherwise = fail "LlvmExport:cast: illegal argument"


-- | Build an integer of the correct size.
make_int :: Int -> Constant
make_int n =
  Int { integerBits = fromIntegral (bitSize (0 :: ArchInt)), integerValue = fromIntegral n }

-- | Create the name of a qualified function.
make_qualified_name :: String -> String -> String
make_qualified_name mod s =
  "_" ++ mod ++ "_" ++ remove_specials s

-- | Return the LLVM integer type of the correct size.
int_type :: Type
int_type =
  IntegerType { typeBits = fromIntegral (bitSize (0 :: ArchInt)) :: Word32 }

-- | Return the LLVM int ptr type (of the correct size).
ptr_type :: Type
ptr_type =
  PointerType {
    pointerReferent = int_type,
    pointerAddrSpace = AddrSpace 0
  }

-- | Return the LLVM type of a function taking [args] arguments.
fun_type :: [a] -> Type
fun_type args =
  FunctionType {
    resultType = int_type,
    argumentTypes = List.replicate (List.length args) int_type,
    isVarArg = False
  }




-- | Proceed to the declaration of the global variables.
define_globals :: [Variable] -> QpState [Definition]
define_globals [] =
  return []
define_globals (gx:gxs) = do
  ngx <- variable_name gx
  mod <- variable_module gx
  gxs <- define_globals gxs
  let gname = make_qualified_name mod ngx
  return $ (GlobalDefinition globalVariableDefaults {
    name = Name gname,
    linkage = External,
    isConstant = False,
    G.type' = int_type
  }):gxs



-- | Proceed to the declaration of the module fucntions.
define_members :: Linkage -> IntMap (Typ, Operand) -> [(Variable, [Variable], CExpr)] -> QpState [Definition]
define_members _ _ [] =
  return []
define_members linkage ctx ((f, arg, cf):fs) = do
  nf <- variable_name f
  fs <- define_members linkage ctx fs
  -- Function name.
  fname <- case linkage of
        External -> do
            mod <- variable_module f
            return $ make_qualified_name mod nf
        _ -> return $ remove_specials nf
  -- Function arguments.
  (param, ctx) <- List.foldr (\a rec -> do
        (as,ctx) <- rec
        na <- variable_name a
        return ((Parameter int_type (Name na) []):as, IMap.insert a (TyInt, LocalReference int_type $ Name na) ctx)) (return ([], ctx)) arg
  -- Function body.
  (ins, term, blocks) <- cexpr_to_llvm ctx cf
  return $ (GlobalDefinition $ functionDefaults {
    linkage = linkage,
    returnType = int_type,
    name = Name fname,
    parameters = (param, False),
    basicBlocks = (BasicBlock (Name "_Mn") ins term):blocks
  }):fs



-- | Convert a continuation value to a callable operand.
value_to_callable_operand :: IntMap (Typ, Operand)
                          -> Typ
                          -> Value
                          -> QpState (CallableOperand, [Named Instruction])
value_to_callable_operand ctx typ (VVar f) = do
  case IMap.lookup f ctx of
    Just (typ', op) -> cast op typ' typ >>= return . \(a,b) -> (Right a, b)
    Nothing -> do
        nf <- variable_name f
        return (Right $ ConstantOperand $ GlobalReference VoidType $ Name nf, [])
value_to_callable_operand ctx typ (VLabel f) = do
  case IMap.lookup f ctx of
    Just (typ', op) -> cast op typ' typ >>= return . \(a,b) -> (Right a, b)
    Nothing -> do
        nf <- variable_name f
        mod <- variable_module f
        return (Right $ ConstantOperand $ GlobalReference VoidType $ Name (make_qualified_name mod nf), [])
value_to_callable_operand _ _ _ =
  fail "LlvmExport:value_to_callable_operand: illegal argument"


-- | Convert a continuation value to an operand.
value_to_operand :: IntMap (Typ, Operand)
                 -> Typ
                 -> Value
                 -> QpState (Operand, [Named Instruction])
value_to_operand ctx typ (VVar f) = do
  case IMap.lookup f ctx of
    Just (typ', op) -> cast op typ' typ
    Nothing -> do
        nf <- variable_name f
        return (LocalReference VoidType $ Name nf, [])
value_to_operand ctx typ (VLabel f) = do
  case IMap.lookup f ctx of
    Just (typ', op) -> cast op typ' typ
    Nothing -> do
        nf <- variable_name f
        mod <- variable_module f
        let op = ConstantOperand $ GlobalReference VoidType $ Name (make_qualified_name mod nf)
        cast op (TyFun []) typ
value_to_operand ctx typ (VGlobal f) = do
  case IMap.lookup f ctx of
    Just (typ', op) -> cast op typ' typ
    Nothing -> do
        nf <- variable_name f
        mod <- variable_module f
        let op = ConstantOperand $ GlobalReference VoidType $ Name (make_qualified_name mod nf)
        cast op TyPtr typ
value_to_operand _ TyInt (VInt n) =
  return (ConstantOperand $ make_int n, [])
value_to_operand _ _ _ =
  fail "LlvmExport:value_to_operand: illegal argument"

-- | An indication of the type of objects.
data Typ =
    TyInt                 -- ^ The object is an integer.
  | TyPtr                 -- ^ The object is a pointer.
  | forall a.TyFun [a]    -- ^ The object is a function with length [a] arguments.

instance Eq Typ where
  TyInt == TyInt = True
  TyPtr == TyPtr = True
  TyFun _ == TyFun _ = True
  _ == _ = False



-- | Convert a CPS expression to LLVM code.
cexpr_to_llvm :: IntMap (Typ,Operand)                                              -- ^ The type and operand of the objects in context.
              -> CExpr                                                             -- ^ Continuation expression.
              -> QpState ([Named Instruction], Named Terminator, [BasicBlock])     -- ^ The result is a terminating llvm code, along with a list of completed blocks.
cexpr_to_llvm _ (CFun _ _ _ _) =
  fail "LlvmExport:cexpr_to_llvm: illegal argument"

cexpr_to_llvm ctx (CApp f args x c) = do
  -- If needed, cast the operand f into a function type.
  (opf,cast) <- value_to_callable_operand ctx (TyFun args) f
  -- The arguments may have to be casted into integers to match the type of the function.
  (args, cins) <- List.foldr (\a rec -> do
        (as, cins) <- rec
        (va, cast) <- value_to_operand ctx TyInt a
        return (va:as, cast ++ cins)
    ) (return ([], [])) args
  nx <- variable_name x
  (ins, term, blocks) <- cexpr_to_llvm (IMap.insert x (TyInt, LocalReference int_type $ Name nx) ctx) c
  return (cast ++ cins ++ [Name nx := call False opf args] ++ ins, term, blocks)

cexpr_to_llvm ctx (CTailApp f args) = do
  -- Same as CApp.
  (opf, cast) <- value_to_callable_operand ctx (TyFun args) f
  -- Same as CApp.
  (args, cins) <- List.foldr (\a rec -> do
        (as, cins) <- rec
        (va, cast) <- value_to_operand ctx TyInt a
        return (va:as, cast ++ cins)
    ) (return ([], [])) args
  x <- create_var "tmp"
  return (cast ++ cins ++ [UnName (fromIntegral x) := call True opf args],
           Do $ Ret (Just $ LocalReference VoidType $ UnName $ fromIntegral x) [], [])

cexpr_to_llvm ctx (CTuple vlist x c) = do
  -- Allocate space for the tuple, and cast the result to int type.
  nx <- variable_name x
  addr <- create_var "tmp" >>= variable_name
  ptr <- malloc (List.length vlist) addr
  let cast = Name nx := PtrToInt (LocalReference int_type $ Name addr) int_type []
  -- Translate the continuation.
  (ins, term, blocks) <- cexpr_to_llvm (IMap.insert x (TyInt, LocalReference int_type $ Name nx) ctx) c
  -- Store the values into the allocated array.
  ins <- List.foldl (\rec (n, v) -> do
        ins <- rec
        tmp <- create_var "tmp"
        (opv, cins) <- value_to_operand ctx TyInt v
        return $ cins ++ [UnName (fromIntegral tmp) := GetElementPtr {
          inBounds = False,
          address = LocalReference VoidType $ Name addr,
          indices = [ConstantOperand $ make_int n],
          metadata = []
         }, Do $ Store {
          volatile = False,
          address = LocalReference VoidType $ UnName (fromIntegral tmp),
          A.value = opv,
          maybeAtomicity = Nothing,
          A.alignment = 0,
          metadata = []
        }] ++ ins) (return ins) $ List.zip [0..List.length vlist-1] vlist
  return (ptr:cast:ins, term, blocks)

cexpr_to_llvm ctx (CFree x c) = do
  -- vx <- value_to_operand x
  -- XXX The free instruction is ignored for the moment. XXX --
  cexpr_to_llvm ctx c

cexpr_to_llvm ctx (CAccess n x y c) = do
  (opx, cast) <- value_to_operand ctx TyPtr x
  ny <- variable_name y
  tmp <- create_var "tmp"
  (ins, term, blocks) <- cexpr_to_llvm (IMap.insert y (TyInt, LocalReference int_type $ Name ny) ctx) c
  return (cast ++ ((UnName (fromIntegral tmp) := GetElementPtr {
    inBounds = False,
    address = opx,
    indices = [ConstantOperand $ make_int n],
    metadata = []
  }):(Name ny := Load {
    volatile = False,
    address = LocalReference VoidType $ UnName (fromIntegral tmp),
    maybeAtomicity = Nothing,
    A.alignment = 0,
    metadata = []
  }):ins), term, blocks)

cexpr_to_llvm ctx (CSwitch x clist def) = do
  -- Translate the value v. [vx] should already be of type int.
  (vx,_) <- value_to_operand ctx TyInt x
  -- Build the block corresponding to the default case.
  ndef <- create_var "_def"
  ndef <- variable_name ndef
  (ins, term, blocks) <- cexpr_to_llvm ctx def
  let dblocks = (BasicBlock (Name ndef) ins term):blocks
  -- Build the blocks corresponding to the other cases.
  (dests, blocks) <- List.foldl (\rec (n, c) -> do
        (dests, bs) <- rec
        (ins, term, blocks) <- cexpr_to_llvm ctx c
        nc <- create_var $ "_L" ++ show n ++ "_"
        nc <- variable_name nc
        return ((make_int n, Name nc):dests,
                [BasicBlock (Name nc) ins term] ++ blocks ++ bs)) (return ([], dblocks)) clist
  return ([], Do $ Switch {
    operand0' = vx,
    defaultDest = Name ndef,
    dests = dests,
    metadata' = []
  }, blocks)

cexpr_to_llvm ctx (CSet x v) = do
  -- [x] is already a pointer, no need for a cast.
  (vx,_) <- value_to_operand ctx TyPtr (VVar x)
  -- Cast [v] to int.
  (vv, cast) <- value_to_operand ctx TyInt v
  return (cast ++ [Do $ Store {
    volatile = False,
    address = vx,
    A.value = vv,
    maybeAtomicity = Nothing,
    A.alignment = 0,
    metadata = []
  }], Do $ Ret {
    returnOperand = Just $ ConstantOperand $ make_int 0,
    metadata' = []
  }, [])

cexpr_to_llvm ctx (CRet v) = do
  -- Cast [v] to int.
  (vv, cast) <- value_to_operand ctx TyInt v
  return (cast, Do $ Ret {
    returnOperand = Just vv,
    metadata' = []
  }, [])

cexpr_to_llvm _ (CError msg) = do
--  withStringNul msg $ \msg -> do
--    err <- externFunction "_Builtins_ERROR" :: CodeGenFunction r (Function (Ptr Word8 -> IO ArchInt))
--    tmp <- getElementPtr0 msg (0 :: Word32, ())
--    _ <- call err tmp
--    ret (fromIntegral 0 :: ArchInt)
  return ([], Do $ Ret {
    returnOperand = Just $ ConstantOperand $ make_int 0,
    metadata' = []
  }, [])



-- | Convert a whole compilation unit to llvm.
cunit_to_llvm :: String     -- ^ Module name.
              -> CUnit      -- ^ Body of the module.
              -> [String]   -- ^ Module dependencies.
              -> String     -- ^ Output file.
              -> QpState ()
cunit_to_llvm mods cu depend filepath = do
  -- Form a map with the local function definitions.
  ctx <- List.foldl (\rec (f, arg, _) -> do
        ctx <- rec
        nf <- variable_name f
        let op = ConstantOperand $ GlobalReference VoidType $ Name nf
        return $ IMap.insert f (TyFun arg, op) ctx) (return IMap.empty) $ local cu
  -- Add the extern functions.
  ctx <- List.foldl (\rec (f, arg, _) -> do
        ctx <- rec
        nf <- variable_name f
        mod <- variable_module f
        let op = ConstantOperand $ GlobalReference VoidType $ Name $ make_qualified_name mod nf
        return $ IMap.insert f (TyFun arg, op) ctx) (return ctx) $ extern cu

  -- Declare the global variables.
  gdef <- define_globals $ List.map fst $ vglobals cu
  -- Define the functions, local and extern.
  ldef <- define_members Private ctx $ local cu
  edef <- define_members External ctx $ extern cu
  -- Define the imported members.
  idef <- List.foldl (\rec f -> do
        idef <- rec
        case f of
          VLabel f -> do
              nf <- variable_name f
              mod <- variable_module f
              return $ (GlobalDefinition functionDefaults {
                name = Name $ make_qualified_name mod nf,
                linkage = External,
                parameters = ([Parameter int_type (UnName 0) [], Parameter int_type (UnName 1) []], False),
                returnType = int_type
              }):idef
          VGlobal g -> do
              ng <- variable_name g
              mod <- variable_module g
              return $ (GlobalDefinition globalVariableDefaults {
                name = Name $ make_qualified_name mod ng,
                linkage = External,
                G.type' = int_type
              }):idef
          _ -> fail "LlvmExport:cunit_to_llvm: illegal import"
    ) (return []) $ C.imports cu
  -- Define the module initializer.
  (igdef, ins) <- List.foldl (\rec (g, cinit) -> do
        (igdef, ins) <- rec
        ng <- variable_name g
        (gins, term, blocks) <- cexpr_to_llvm IMap.empty cinit
        let init = Right $ LocalReference VoidType $ Name ("init" ++ make_qualified_name mods ng)
        return ((GlobalDefinition functionDefaults {
          name = Name $ "init" ++ make_qualified_name mods ng,
          returnType = int_type,
          basicBlocks = (BasicBlock (Name "_Mn") gins term):blocks
        }):igdef, (Do $ call False init []):ins) ) (return ([], [])) $ vglobals cu
  let initdef = GlobalDefinition functionDefaults {
    name = Name $ "init" ++ mods,
    returnType = int_type,
    basicBlocks = [BasicBlock (Name "_Mn") ins (Do $ Ret { returnOperand = Just $ ConstantOperand $ make_int 0, metadata' = [] })]
  }
  -- Define malloc and free.
  let cdef = [GlobalDefinition functionDefaults {
      name = Name "malloc",
      returnType = ptr_type,
      parameters = ([Parameter int_type (Name "") []], False)
    }, GlobalDefinition functionDefaults {
      name = Name "free",
      returnType = int_type,
      parameters = ([Parameter ptr_type (Name "") []], False)
    }]

  -- Define the main function.
  mdef <- case main cu of
        Just body -> do
            -- Global variable initialization.
            (ndef, dins) <- List.foldl (\rec dep -> do
                  (ndef, ins) <- rec
                  let initdep = GlobalDefinition functionDefaults {
                    name =  Name ("init" ++ dep),
                    returnType = int_type
                  }
                  let init = Right $ LocalReference VoidType $ Name ("init" ++ dep)
                  return (initdep:ndef,
                          (Do $ call False init []):ins)) (return ([],[])) $ List.reverse depend
            -- Body of the main.
            (bins, term, blocks) <- cexpr_to_llvm IMap.empty body

            return $ (GlobalDefinition functionDefaults {
              name = Name "main",
              returnType = int_type,
              basicBlocks = (BasicBlock (Name "_Mn") (dins ++ bins) term):blocks
            }):ndef
        Nothing -> return []

  -- Assemble the definitions and buid the module.
  let astmod  = Module {
    moduleName = mods,
    moduleDataLayout = Nothing,
    moduleTargetTriple = Nothing,
    moduleDefinitions = cdef ++ idef ++ gdef ++ ldef ++ edef ++ igdef ++ [initdef] ++ mdef
  }

  Monad.QpState.liftIO $ withContext $ \context ->
    liftError $ withModuleFromAST context astmod $ \m -> do
      str <- moduleBitcode m
      Data.ByteString.writeFile (filepath ++ ".bc") str
      return ()

    where
      liftError :: ExceptT String IO a -> IO a
      liftError e = do
        r <- runExceptT e
        either fail return r


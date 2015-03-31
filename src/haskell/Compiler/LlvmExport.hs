{-# LANGUAGE CPP, ScopedTypeVariables, ExistentialQuantification #-}

-- | This module contains the functions necessary for the production of LLVM code.
module Compiler.LlvmExport where

import Utils
import Classes

import Compiler.Continuations as C

import Monad.Core (variableName, variableModule)
import Monad.Compiler
import Monad.Error

import LLVM.General.AST as A
import LLVM.General.AST.Global hiding (callingConvention, returnAttributes, functionAttributes)
import qualified LLVM.General.AST.Global as G
import LLVM.General.AST.Constant as AC (Constant(Int, GlobalReference), integerBits, integerValue)
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

import Control.Monad.Trans
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
malloc :: Int -> String -> Compiler (Named A.Instruction)
malloc size retval =
  return $ Name retval := A.Call {
    isTailCall = False,
    callingConvention = C,
    returnAttributes = [],
    function = Right $ ConstantOperand $ GlobalReference VoidType $ Name "malloc",
    arguments = [(ConstantOperand $ makeInt (size * bitSize (0 :: ArchInt) `quot` 8), [])],
    functionAttributes = [],
    metadata = []
  }

-- | Create a Call instruction.
call :: Bool -> CallableOperand -> [Operand] -> A.Instruction
call tail func arg =
  A.Call {
    isTailCall = tail,
    callingConvention = C,
    returnAttributes = [],
    function = func,
    arguments = List.map (\a -> (a,[])) arg,
    functionAttributes = [],
    metadata = []
  }

-- | Cast an operand of some type into another.
cast :: Operand -> Typ -> Typ -> Compiler (Operand, [Named A.Instruction])
cast op TyInt TyPtr = do
  tmp <- createVariable "tmp"
  let nop = LocalReference intType $ UnName $ fromIntegral tmp
  return (nop, [UnName (fromIntegral tmp) := IntToPtr op ptrType []])
cast op TyInt (TyFun arg) = do
  tmp <- createVariable "tmp"
  let nop = LocalReference intType $ UnName $ fromIntegral tmp
  return (nop, [UnName (fromIntegral tmp) := IntToPtr op (PointerType (funType arg) (AddrSpace 0)) []])
cast op TyPtr TyInt = do
  tmp <- createVariable "tmp"
  let nop = LocalReference VoidType $ UnName $ fromIntegral tmp
  return (nop, [UnName (fromIntegral tmp) := PtrToInt op intType []])
cast op (TyFun _) TyInt = do
  tmp <- createVariable "tmp"
  let nop = LocalReference VoidType $ UnName $ fromIntegral tmp
  return (nop, [UnName (fromIntegral tmp) := PtrToInt op intType []])
cast op ty ty' | ty == ty' = return (op, [])
               | otherwise = fail "LlvmExport:cast: illegal argument"


-- | Build an integer of the correct size.
makeInt :: Int -> AC.Constant
makeInt n =
  Int { integerBits = fromIntegral (bitSize (0 :: ArchInt)), integerValue = fromIntegral n }

-- | Create the name of a qualified function.
makeQualifiedName :: String -> String -> String
makeQualifiedName mod s =
  "_" ++ mod ++ "_" ++ remove_specials s

-- | Return the LLVM integer type of the correct size.
intType :: Type
intType =
  IntegerType { typeBits = fromIntegral (bitSize (0 :: ArchInt)) :: Word32 }

-- | Return the LLVM int ptr type (of the correct size).
ptrType :: Type
ptrType =
  PointerType {
    pointerReferent = intType,
    pointerAddrSpace = AddrSpace 0
  }

-- | Return the LLVM type of a function taking [args] arguments.
funType :: [a] -> Type
funType args =
  FunctionType {
    resultType = intType,
    argumentTypes = List.replicate (List.length args) intType,
    isVarArg = False
  }




-- | Proceed to the declaration of the global variables.
defineGlobals :: [Variable] -> Compiler [Definition]
defineGlobals [] =
  return []
defineGlobals (gx:gxs) = do
  ngx <- runCore $ variableName gx
  mod <- runCore $ variableModule gx
  gxs <- defineGlobals gxs
  let gname = makeQualifiedName mod ngx
  return $ (GlobalDefinition globalVariableDefaults {
    name = Name gname,
    linkage = External,
    isConstant = False,
    G.type' = intType
  }):gxs



-- | Proceed to the declaration of the module fucntions.
defineMembers :: Linkage -> IntMap (Typ, Operand) -> [(Variable, [Variable], C.Instruction)] -> Compiler [Definition]
defineMembers _ _ [] =
  return []
defineMembers linkage ctx ((f, arg, cf):fs) = do
  nf <- runCore $ variableName f
  fs <- defineMembers linkage ctx fs
  -- Function name.
  fname <- case linkage of
        External -> do
            mod <- runCore $ variableModule f
            return $ makeQualifiedName mod nf
        _ -> return $ remove_specials nf
  -- Function arguments.
  (param, ctx) <- List.foldr (\a rec -> do
        (as,ctx) <- rec
        na <- runCore $ variableName a
        return ((Parameter intType (Name na) []):as, IMap.insert a (TyInt, LocalReference intType $ Name na) ctx)) (return ([], ctx)) arg
  -- Function body.
  (ins, term, blocks) <- instructionToLlvm ctx cf
  return $ (GlobalDefinition $ functionDefaults {
    linkage = linkage,
    returnType = intType,
    name = Name fname,
    parameters = (param, False),
    basicBlocks = (BasicBlock (Name "_Mn") ins term):blocks
  }):fs



-- | Convert a continuation value to a callable operand.
valueToCallableOperand :: IntMap (Typ, Operand)
                          -> Typ
                          -> Value
                          -> Compiler (CallableOperand, [Named A.Instruction])
valueToCallableOperand ctx typ (VVar f) = do
  case IMap.lookup f ctx of
    Just (typ', op) -> cast op typ' typ >>= return . \(a,b) -> (Right a, b)
    Nothing -> do
        nf <- runCore $ variableName f
        return (Right $ ConstantOperand $ GlobalReference VoidType $ Name nf, [])
valueToCallableOperand ctx typ (VLabel f) = do
  case IMap.lookup f ctx of
    Just (typ', op) -> cast op typ' typ >>= return . \(a,b) -> (Right a, b)
    Nothing -> do
        nf <- runCore $ variableName f
        mod <- runCore $ variableModule f
        return (Right $ ConstantOperand $ GlobalReference VoidType $ Name (makeQualifiedName mod nf), [])
valueToCallableOperand _ _ _ =
  fail "LlvmExport:valueToCallableOperand: illegal argument"


-- | Convert a continuation value to an operand.
valueToOperand :: IntMap (Typ, Operand)
                 -> Typ
                 -> Value
                 -> Compiler (Operand, [Named A.Instruction])
valueToOperand ctx typ (VVar f) = do
  case IMap.lookup f ctx of
    Just (typ', op) -> cast op typ' typ
    Nothing -> do
        nf <- runCore $ variableName f
        return (LocalReference VoidType $ Name nf, [])
valueToOperand ctx typ (VLabel f) = do
  case IMap.lookup f ctx of
    Just (typ', op) -> cast op typ' typ
    Nothing -> do
        nf <- runCore $ variableName f
        mod <- runCore $ variableModule f
        let op = ConstantOperand $ GlobalReference VoidType $ Name (makeQualifiedName mod nf)
        cast op (TyFun []) typ
valueToOperand ctx typ (VGlobal f) = do
  case IMap.lookup f ctx of
    Just (typ', op) -> cast op typ' typ
    Nothing -> do
        nf <- runCore $ variableName f
        mod <- runCore $ variableModule f
        let op = ConstantOperand $ GlobalReference VoidType $ Name (makeQualifiedName mod nf)
        cast op TyPtr typ
valueToOperand _ TyInt (VInt n) =
  return (ConstantOperand $ makeInt n, [])
valueToOperand _ _ _ =
  fail "LlvmExport:valueToOperand: illegal argument"

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
instructionToLlvm :: IntMap (Typ,Operand)                                              -- ^ The type and operand of the objects in context.
              -> C.Instruction                                                             -- ^ Continuation expression.
              -> Compiler ([Named A.Instruction], Named Terminator, [BasicBlock])     -- ^ The result is a terminating llvm code, along with a list of completed blocks.
instructionToLlvm _ (C.Function _ _ _ _) =
  fail "LlvmExport:instructionToLlvm: illegal argument"

instructionToLlvm ctx (C.Call f args x c) = do
  -- If needed, cast the operand f into a function type.
  (opf,cast) <- valueToCallableOperand ctx (TyFun args) f
  -- The arguments may have to be casted into integers to match the type of the function.
  (args, cins) <- List.foldr (\a rec -> do
        (as, cins) <- rec
        (va, cast) <- valueToOperand ctx TyInt a
        return (va:as, cast ++ cins)
    ) (return ([], [])) args
  nx <- runCore $ variableName x
  (ins, term, blocks) <- instructionToLlvm (IMap.insert x (TyInt, LocalReference intType $ Name nx) ctx) c
  return (cast ++ cins ++ [Name nx := call False opf args] ++ ins, term, blocks)

instructionToLlvm ctx (C.TailCall f args) = do
  -- Same as CApp.
  (opf, cast) <- valueToCallableOperand ctx (TyFun args) f
  -- Same as CApp.
  (args, cins) <- List.foldr (\a rec -> do
        (as, cins) <- rec
        (va, cast) <- valueToOperand ctx TyInt a
        return (va:as, cast ++ cins)
    ) (return ([], [])) args
  x <- createVariable "tmp"
  return (cast ++ cins ++ [UnName (fromIntegral x) := call True opf args],
           Do $ A.Ret (Just $ LocalReference VoidType $ UnName $ fromIntegral x) [], [])

instructionToLlvm ctx (C.Array vlist x c) = do
  -- Allocate space for the tuple, and cast the result to int type.
  nx <- runCore $ variableName x
  tmp <- createVariable "tmp"
  addr <- runCore $ variableName tmp
  ptr <- malloc (List.length vlist) addr
  let cast = Name nx := PtrToInt (LocalReference intType $ Name addr) intType []
  -- Translate the continuation.
  (ins, term, blocks) <- instructionToLlvm (IMap.insert x (TyInt, LocalReference intType $ Name nx) ctx) c
  -- Store the values into the allocated array.
  ins <- List.foldl (\rec (n, v) -> do
        ins <- rec
        tmp <- createVariable "tmp"
        (opv, cins) <- valueToOperand ctx TyInt v
        return $ cins ++ [UnName (fromIntegral tmp) := GetElementPtr {
          inBounds = False,
          address = LocalReference VoidType $ Name addr,
          indices = [ConstantOperand $ makeInt n],
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

instructionToLlvm ctx (C.Access n x y c) = do
  (opx, cast) <- valueToOperand ctx TyPtr x
  ny <- runCore $ variableName y
  tmp <- createVariable "tmp"
  (ins, term, blocks) <- instructionToLlvm (IMap.insert y (TyInt, LocalReference intType $ Name ny) ctx) c
  return (cast ++ ((UnName (fromIntegral tmp) := GetElementPtr {
    inBounds = False,
    address = opx,
    indices = [ConstantOperand $ makeInt n],
    metadata = []
  }):(Name ny := Load {
    volatile = False,
    address = LocalReference VoidType $ UnName (fromIntegral tmp),
    maybeAtomicity = Nothing,
    A.alignment = 0,
    metadata = []
  }):ins), term, blocks)

instructionToLlvm ctx (C.Switch x clist def) = do
  -- Translate the value v. [vx] should already be of type int.
  (vx,_) <- valueToOperand ctx TyInt x
  -- Build the block corresponding to the default case.
  ndef <- createVariable "_def"
  ndef <- runCore $ variableName ndef
  (ins, term, blocks) <- instructionToLlvm ctx def
  let dblocks = (BasicBlock (Name ndef) ins term):blocks
  -- Build the blocks corresponding to the other cases.
  (dests, blocks) <- List.foldl (\rec (n, c) -> do
        (dests, bs) <- rec
        (ins, term, blocks) <- instructionToLlvm ctx c
        nc <- createVariable $ "_L" ++ show n ++ "_"
        nc <- runCore $ variableName nc
        return ((makeInt n, Name nc):dests,
                [BasicBlock (Name nc) ins term] ++ blocks ++ bs)) (return ([], dblocks)) clist
  return ([], Do $ A.Switch {
    operand0' = vx,
    defaultDest = Name ndef,
    dests = dests,
    metadata' = []
  }, blocks)

instructionToLlvm ctx (C.Set x v) = do
  -- [x] is already a pointer, no need for a cast.
  (vx,_) <- valueToOperand ctx TyPtr (VVar x)
  -- Cast [v] to int.
  (vv, cast) <- valueToOperand ctx TyInt v
  return (cast ++ [Do $ Store {
    volatile = False,
    address = vx,
    A.value = vv,
    maybeAtomicity = Nothing,
    A.alignment = 0,
    metadata = []
  }], Do $ A.Ret {
    returnOperand = Just $ ConstantOperand $ makeInt 0,
    metadata' = []
  }, [])

instructionToLlvm ctx (C.Ret v) = do
  -- Cast [v] to int.
  (vv, cast) <- valueToOperand ctx TyInt v
  return (cast, Do $ A.Ret {
    returnOperand = Just vv,
    metadata' = []
  }, [])

instructionToLlvm _ (C.Error msg) = do
--  withStringNul msg $ \msg -> do
--    err <- externFunction "_Builtins_ERROR" :: CodeGenFunction r (Function (Ptr Word8 -> IO ArchInt))
--    tmp <- getElementPtr0 msg (0 :: Word32, ())
--    _ <- call err tmp
--    ret (fromIntegral 0 :: ArchInt)
  return ([], Do $ A.Ret {
    returnOperand = Just $ ConstantOperand $ makeInt 0,
    metadata' = []
  }, [])



-- | Convert a whole compilation unit to llvm.
unitToLlvm :: String     -- ^ Module name.
              -> CompilationUnit      -- ^ Body of the module.
              -> [String]   -- ^ Module dependencies.
              -> String     -- ^ Output file.
              -> Compiler ()
unitToLlvm mods cu depend filepath = do
  -- Form a map with the local function definitions.
  ctx <- List.foldl (\rec (f, arg, _) -> do
        ctx <- rec
        nf <- runCore $ variableName f
        let op = ConstantOperand $ GlobalReference VoidType $ Name nf
        return $ IMap.insert f (TyFun arg, op) ctx) (return IMap.empty) $ localFunctions cu
  -- Add the extern functions.
  ctx <- List.foldl (\rec (f, arg, _) -> do
        ctx <- rec
        nf <- runCore $ variableName f
        mod <- runCore $ variableModule f
        let op = ConstantOperand $ GlobalReference VoidType $ Name $ makeQualifiedName mod nf
        return $ IMap.insert f (TyFun arg, op) ctx) (return ctx) $ externFunctions cu

  -- Declare the global variables.
  gdef <- defineGlobals $ List.map fst $ globalVariables cu
  -- Define the functions, local and extern.
  ldef <- defineMembers Private ctx $ localFunctions cu
  edef <- defineMembers External ctx $ externFunctions cu
  -- Define the imported members.
  idef <- List.foldl (\rec f -> do
        idef <- rec
        case f of
          VLabel f -> do
              nf <- runCore $ variableName f
              mod <- runCore $ variableModule f
              return $ (GlobalDefinition functionDefaults {
                name = Name $ makeQualifiedName mod nf,
                linkage = External,
                parameters = ([Parameter intType (UnName 0) [], Parameter intType (UnName 1) []], False),
                returnType = intType
              }):idef
          VGlobal g -> do
              ng <- runCore $ variableName g
              mod <- runCore $ variableModule g
              return $ (GlobalDefinition globalVariableDefaults {
                name = Name $ makeQualifiedName mod ng,
                linkage = External,
                G.type' = intType
              }):idef
          _ -> fail "LlvmExport:unitToLlvm: illegal import"
    ) (return []) $ C.imports cu
  -- Define the module initializer.
  (igdef, ins) <- List.foldl (\rec (g, cinit) -> do
        (igdef, ins) <- rec
        ng <- runCore $ variableName g
        (gins, term, blocks) <- instructionToLlvm IMap.empty cinit
        let init = Right $ LocalReference VoidType $ Name ("init" ++ makeQualifiedName mods ng)
        return ((GlobalDefinition functionDefaults {
          name = Name $ "init" ++ makeQualifiedName mods ng,
          returnType = intType,
          basicBlocks = (BasicBlock (Name "_Mn") gins term):blocks
        }):igdef, (Do $ call False init []):ins) ) (return ([], [])) $ globalVariables cu
  let initdef = GlobalDefinition functionDefaults {
    name = Name $ "init" ++ mods,
    returnType = intType,
    basicBlocks = [BasicBlock (Name "_Mn") ins (Do $ A.Ret { returnOperand = Just $ ConstantOperand $ makeInt 0, metadata' = [] })]
  }
  -- Define malloc and free.
  let cdef = [GlobalDefinition functionDefaults {
      name = Name "malloc",
      returnType = ptrType,
      parameters = ([Parameter intType (Name "") []], False)
    }, GlobalDefinition functionDefaults {
      name = Name "free",
      returnType = intType,
      parameters = ([Parameter ptrType (Name "") []], False)
    }]

  -- Define the main function.
  mdef <- case main cu of
        Just body -> do
            -- Global variable initialization.
            (ndef, dins) <- List.foldl (\rec dep -> do
                  (ndef, ins) <- rec
                  let initdep = GlobalDefinition functionDefaults {
                    name =  Name ("init" ++ dep),
                    returnType = intType
                  }
                  let init = Right $ LocalReference VoidType $ Name ("init" ++ dep)
                  return (initdep:ndef,
                          (Do $ call False init []):ins)) (return ([],[])) $ List.reverse depend
            -- Body of the main.
            (bins, term, blocks) <- instructionToLlvm IMap.empty body

            return $ (GlobalDefinition functionDefaults {
              name = Name "main",
              returnType = intType,
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

  runCore $ lift $ withContext $ \context ->
    liftError $ withModuleFromAST context astmod $ \m -> do
      str <- moduleBitcode m
      Data.ByteString.writeFile (filepath ++ ".bc") str
      return ()

    where
      liftError :: ExceptT String IO a -> IO a
      liftError e = do
        r <- runExceptT e
        either fail return r


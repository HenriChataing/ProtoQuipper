-- | This module provides an interface to the type inference and unification algorithms. It introduces functions to
-- parse and process modules, and to deal with module dependencies.
module Driver where

import Classes
import Utils
import Options
import Builtins

import Language.Constructor as Constructor

import Parsing.Lexer
import qualified Parsing.Parser as P
import qualified Parsing.Syntax as S
import Parsing.Location (unknownExtent)
import Parsing.Printer

import Core.Syntax
import Core.Translate as Translate
import Core.Environment as Environment (Environment, constructors)
import Core.Namespace as Namespace (constructors)

import Interpreter.Interpreter hiding (Environment)
import Interpreter.Values
import Interpreter.IRExport
import Interpreter.Circuits

import Typer.Ordering
import Typer.Subtyping
import Typer.TypeInference
import Typer.TypingContext

import Compiler.PatternElimination as PatternElimination
import Compiler.Overloading as Overloading
import Compiler.Continuations as Continuations
import Compiler.LlvmExport

import Monad.Error
import Monad.Core as Core
import Monad.Typer as Typer
import Monad.Interpreter as Interpreter
import Monad.Compiler as Compiler

import System.Directory
import System.FilePath.Posix
import System.Process

import Data.List as List
import Data.Map as Map
import Data.IntMap as IntMap
import Data.Char as Char
import qualified Data.ByteString.Lazy.Internal as BI
import qualified Data.ByteString.Lazy as B
import Control.Monad.Trans.State
import Control.Monad.Trans


-- | Lex and parse the module implementation file at the given filepath.
parseModule :: FilePath -> Core S.Program
parseModule filePath = do
  contents <- lift $ B.readFile filePath
  tokens <- lift $ mylex filePath contents
  let name = moduleNameOfFile filePath
  return $ (P.parse tokens) { S.moduleName = name, S.filePath = filePath }


-- | Explore a list of include directories in order to find the implementation of the requested
-- module. The name of the file is expected to be /dir/\//module/./ext/, where /dir/ is the directory,
-- /module/ is the name of the module (with the first letter changed to lower case), and /ext/ the
-- extension, which can be either @.qp@ (implementation) or @.qpi@ (interface). \'/dir/\' is taken
-- in the provided list of directories. If several implementations are found, an error is raised.
findModule :: String       -- ^ Module name.
          -> [FilePath]    -- ^ List of included directories.
          -> String        -- ^ Extension.
          -> Core FilePath
findModule "" directories extension = do
  fail "Driver:findModule: empty module name"

findModule moduleName directories extension = do
  let moduleFile = fileOfModuleName moduleName extension
  existing <- List.foldl (\rec directory -> do
      found <- rec
      let nexttry = combine directory moduleFile
      exists <- lift $ doesFileExist nexttry
      if exists then
        return (nexttry:found)
      else
        return found
    ) (return []) directories
  case existing of
    -- No implementation found
    [] -> throwNE $ NonExistentModule moduleName
    -- OK
    [path] -> return $ path
    -- Several implementations found
    (path:path':_) -> throwNE $ DuplicateImplementation moduleName path path'


-- | Recursively explore the dependencies of the program. This function returns a map linking the
-- modules to their parsed implementations, and a map corresponding to the dependency graph. It
-- proceeds to sort the dependencies topologically using an in-depth exploration of the graph. Note
-- that the return list is reversed, with the \'oldest\' module first. During the exploration, if
-- a module is visited that had already been explored but not yet pushed on the sorted list, an error
-- is generated (cyclic dependencies).
findDependencies :: [FilePath]           -- ^ List of included directories.
                -> S.Program             -- ^ Current module.
                -> [String]              -- ^ The list of explored modules.
                -> [S.Program]           -- ^ Modules depending on the current module.
                -> Core ([S.Program], [String])
findDependencies directories prog explored depends = do
  -- Mark the module as explored.
  explored <- return $ (S.moduleName prog):explored
  -- For each dependency, check if it was already loaded, else recursively call findDependencies
  -- on the dependency.
  (depends, explored) <- List.foldl (\rec name -> do
      (depends, explored) <- rec
      case (List.elem name explored, List.find (\prog -> S.moduleName prog == name) depends) of
        -- Ok: depency already met.
        (True, Just _) -> return (depends, explored)
        -- The module has already been visited : cyclic dependency Build the loop : by removing
        -- the already sorted modules, and spliting the explored list at the first visit of this module.
        (True, Nothing) -> do
            Core.flush
            inloop <- return $ explored List.\\ (List.map S.moduleName depends)
            (loop, _) <- return $ List.span (\name' -> name' /= name) inloop
            throwNE $ CircularDependency name $ List.reverse (name:loop)
        -- Explore.
        _ -> do
            file <- findModule name directories ".qp"
            parsedModule <- parseModule file
            findDependencies directories parsedModule explored depends
    ) (return (depends, explored)) (S.imports prog)
  -- Push the module on top of the list : after its dependencies
  return (prog:depends, explored)


-- | Sort the dependencies of file in a topological fashion. The program argument is the main program,
-- on which Proto-Quipper has been called. The return value is a list of the dependencies, with the
-- properties:
--
--     * each module may only appear once;
--
--     * the dependencies of each module are placed before it in the sorted list;
--
--     * the main module is placed last.
--
buildDependencies :: [FilePath]          -- ^ List of directories.
                  -> S.Program           -- ^ Main module.
                  -> Core [S.Program]
buildDependencies directories main = do
  (depends, _) <- findDependencies directories main [] []
  return $ List.reverse depends


-- | Sort the dependencies of a set of modules in a topological fashion. The program argument is the
-- list of programs on which Proto-Quipper has been called. The return value is a list of the dependencies,
-- with the properties:
--
--     * each module may only appear once;
--
--     * the dependencies of each module are placed before it in the sorted list
--
buildSetDependencies :: [FilePath]         -- ^ List of directories.
                    -> [String]            -- ^ Main modules (by name only).
                    -> Core [S.Program]
buildSetDependencies directories modules = do
  depends <- buildDependencies directories S.dummyProgram { S.imports = modules }
  return $ List.init depends


-- | Process a module definition. Depending on the options some of the following steps may be omitted.
--   - conversion from parsing syntax to core syntax (scope analysis)
--   - type inference and type checking
--   - interpretation
--   - compilation
processModule :: (Int, Int) -> S.Program -> Typer ()
processModule (number, total) program = do
  options <- Typer.runCore getOptions
  let moduleName = S.moduleName program
  -- Scope analysis.
  translateState <- Typer.runCore $ Translate.init moduleName $ S.imports program
  (declarations, translateState) <- Typer.runCore $ runStateT (translateDeclarations $ S.body program) translateState
  -- Type inference.
  (declarations, gamma) <- typeDeclarations declarations
  -- Interpretation.
  valuation <- if runInterpreter options then do
      interpreterState <- Interpreter.init $ S.imports program
      (valuation, _) <- runStateT (interpretDeclarations declarations) interpreterState
      return valuation
    else return IntMap.empty
  -- Pack the module definition and insert it into the core monad.
  let mod = Module {
        moduleName = moduleName,
        filePath = S.filePath program,
        Core.environment = Translate.environment translateState,
        Core.typemap = gamma,
        valuation = valuation
        }
  Typer.runCore $ define mod
  -- Compilation.
  if runCompiler options then do
    let outputFile = combine (outputDir options) moduleName
    Typer.runIO $ putStrLn (
        "[ " ++ show number ++ " of " ++ show total ++ " ] Compiling " ++ moduleName ++
        "  (" ++ S.filePath program ++ "," ++ outputFile ++ ".bc)")

    -- Add constructor implementations.
    declarations <- Typer.runCore $ implementConstructors mod declarations
    -- Initial compilation state.
    compilerState <- Compiler.init
    -- Compilation process.
    let compilation = do
          declarations <- Overloading.transformDeclarations declarations
          declarations <- PatternElimination.transformDeclarations declarations
          compilationUnit <- Continuations.convertDeclarations declarations

          if displayIntermediate options then do
            Compiler.runCore $ lift $ putStrLn $ "======   " ++ moduleName ++ "   ======"
            pVar <- Compiler.runCore displayVar
            Compiler.runCore $ lift $ putStrLn $ genprint Inf [pVar] compilationUnit
          else return ()

          unitToLlvm moduleName compilationUnit (S.imports program) outputFile
    (_, _) <- runStateT compilation compilerState
    return ()
  else
    return ()


-- | Explicit the implementation of functional data constructors.
implementConstructors :: Module -> [Declaration] -> Core [Declaration]
implementConstructors mod declarations = do
  Map.foldWithKey (\name cons rec -> do
      declarations <- rec
      info <- getConstructorInfo cons
      if isFunction $ Constructor.typ info then do
        -- Takes an argument -> write an implementation.
        x <- registerVariable (Just $ moduleName mod) "_x"
        y <- registerVariable (Just $ moduleName mod) name
        let e = EFun noTermInfo (PVar noTermInfo x) (EDatacon noTermInfo cons $ Just (EVar noTermInfo x))
        -- Update the definition of cons.
        setConstructorImplementation cons y
        -- Update the module definition
        return $ (DLet noTermInfo Nonrecursive y e):declarations
      -- Takes no argument -> do nothing.
      else return declarations
      ) (return declarations) (Environment.constructors $ Core.environment mod)


-- ==================================== --
-- | A function to do everything!
-- In order to sort the dependencies of a list of modules, and to be able to reuse the existing
-- functions for single modules, a dummy module is created that imports all the top-level modules
-- (never to be executed).
processModules :: [FilePath] -> Typer ()
processModules files = do
  options <- Typer.runCore getOptions
  -- Get the module names.
  let progs = List.map moduleNameOfFile files
  -- Build the dependencies.
  deps <- Typer.runCore $ buildSetDependencies (includeDirs options) progs
  let total = List.length deps

  -- Build the builtin / qlib interfaces.
  Typer.runCore defineBuiltins

  -- Process everything, finishing by the main modules.
  mods <- List.foldl (\rec (n, prog) -> do
      mods <- rec
      -- Module specific options.
      Typer.runCore $ changeOptions $ \options -> options { displayToplevelTypes = False }
      -- Process the module.
      processModule (n, total) prog

    ) (return ()) $ List.zip [1..total] deps

  -- Assemble the compiled files (if needed).
  if runCompiler options then do
    let files = List.map (\prog -> " " ++ combine (outputDir options) (S.moduleName prog) ++ ".bc") deps
        builtin = "foreign/Builtins.bc"
        mainbc = combine (outputDir options) "main.bc"
        mainS = combine (outputDir options) "main.S"
        mains = combine (outputDir options) "main.s"
    Typer.runIO $ putStrLn $ "llvm-link " ++ builtin ++ List.concat files ++ " -o " ++ mainbc
    _ <- Typer.runIO $ (runCommand $ "llvm-link " ++ builtin ++ List.concat files ++ " -o " ++ mainbc) >>= waitForProcess
    Typer.runIO $ putStrLn $ "llc " ++ mainbc ++ " -o " ++ mainS
    _ <- Typer.runIO $ (runCommand $ "llc " ++ mainbc ++ " -o " ++ mainS) >>= waitForProcess
    Typer.runIO $ putStrLn $ "g++ -g " ++ mainS ++ " -o " ++ mains
    _ <- Typer.runIO $ (runCommand $ "g++ -g " ++ mainS ++ " -o " ++ mains) >>= waitForProcess
    return ()
  else return ()

-- ===================================== --

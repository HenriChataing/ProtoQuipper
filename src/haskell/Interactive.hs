{-# LANGUAGE ScopedTypeVariables #-}

-- | This module implements the interactive mode of Proto-Quipper.
module Interactive where

import Options
import Classes
import Console
import Utils
import Driver

import Parsing.Lexer
import Parsing.Parser
import Parsing.Location hiding (location)
import qualified Parsing.Syntax as S

import Core.Syntax
import Core.Translate hiding (environment)
import Core.Environment (Environment, Trace (..))
import qualified Core.Namespace as Namespace (variables)
import qualified Core.Environment as Environment (variables, types, unpack)
import qualified Core.Translate as Translate (environment, types)

import Typer.TypingContext
import Typer.Subtyping
import Typer.TypeInference

import Interpreter.Circuits
import Interpreter.Values (Value)
import Interpreter.Interpreter (interpretDeclaration)

import Monad.Error
import Monad.Core hiding (environment, valuation, typemap)
import Monad.Typer as Typer hiding (runIO, runCore, typemap)
import Monad.Interpreter as Interpreter (Interpreter, circuits, context, load)
import qualified Monad.Core as Core (environment, valuation, typemap)
import qualified Monad.Interpreter as Interpreter (runCore, runTyper, init)

import System.IO

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.IntSet as IntSet
import Data.IntMap as IntMap
import qualified Data.ByteString.Lazy as B

import Control.Exception
import Control.Monad.Trans.State
import Control.Monad.Trans
import Control.Monad.Catch as CM


-- | The interactive mode runs in a specific monad, on top of the interpreter monad.
data InteractiveState = InteractiveState {
  environment :: Environment,
  typemap :: IntMap TypeScheme,
  valuation :: IntMap Value,
  constraints :: ConstraintSet
  --modules :: [String] -- Loaded modules.
}

type Interactive = StateT InteractiveState Interpreter


runCore :: Core a -> Interactive a
runCore computation = lift $ Interpreter.runCore computation

runTyper :: Typer a -> Interactive a
runTyper computation = lift $ Interpreter.runTyper computation

runIO :: IO a -> Interactive a
runIO computation = lift $ Interpreter.runCore $ lift computation


-- Build the interactive initial state.
init :: Core InteractiveState
init = do
  builtins <- require "Builtins"
  return InteractiveState {
      environment = Core.environment builtins,
      typemap = Core.typemap builtins,
      valuation = Core.valuation builtins,
      constraints = emptyset
    }


-- | Extract the context of the scope analysis from the interactive state.
getTranslateState :: Interactive TranslateState
getTranslateState = do
  env <- gets environment
  let typs = Map.map (\id ->
        TypeAnnot 0 $ TypeApply (TypeUser id) []
        ) $ Environment.types env
  return TranslateState {
      bound = True,
      location = unknownExtent,
      Translate.environment = env,
      types = typs,
      currentModule = "Interactive"
    }


-- | Imports a list of modules in the current context. This function is not stupid: if the modules
-- were already imported, it does nothing. However, it does \"reload\" the names in the current
-- labelling map: if one of the global variables /x/ was over-written by a declaration
--
-- @
-- let x = ... ;;
-- @
--
-- it will made available again, thus overwriting the above mapping.
importModules :: [String] -> Interactive ()
importModules moduleNames = do
  options <- runCore getOptions
  -- Build the dependencies (with a dummy module that is removed immediately).
  depends <- runCore $ buildSetDependencies (includeDirs options) moduleNames
  List.foldl (\rec program -> do
      rec
      -- If the module has been explicitly included, import the declarations in the state.
      if List.elem (S.moduleName program) moduleNames then do
        runTyper $ withOptions (\options ->
            options { displayToplevelTypes = True, evalToplevelExprs = True }) $ processModule (0, 0) program
        mod <- runCore $ require $ S.moduleName program
        -- Import.
        modify $ \state -> state {
            environment = (environment state) <+> (Environment.unpack $ Core.environment mod),
            typemap = IntMap.union (typemap state) (Core.typemap mod),
            valuation = IntMap.union (valuation state) (Core.valuation mod)
          }
      else do
        -- Check whether the module has already been imported or not.
        mod <- runCore $ requireSafe $ S.moduleName program
        -- Process the module if needed.
        case mod of
          Just _ -> return ()
          Nothing -> do
            let setOptions = \options ->
                  options {
                    displayToplevelTypes = False,
                    evalToplevelExprs = False
                  }
            runTyper $ withOptions setOptions $ processModule (0, 0) program
        -- Load the module in the interpreter state.
        lift $ Interpreter.load $ S.moduleName program
    ) (return ()) depends


-- | Process a user command. Since the command is like a module implementation, it is dealt with the
-- same way. The only exception concerns import declarations, which are handled specifically by the
-- function 'Interactive.importModules'.
runCommand :: S.Program -> Interactive ()
runCommand program = do
  -- Import the modules.
  importModules (S.imports program)
  -- Scope analysis.
  state <- getTranslateState
  (declarations, state) <- runCore $ runStateT (translateDeclarations $ S.body program) state
  -- Type inference and interpretation.
  inter <- get
  (gamma, env, cset) <- List.foldl (\rec decl -> do
      (gamma, env, cset) <- rec
      (decl, cset, gamma) <- runTyper $ typeDeclaration cset gamma decl -- Type inference.
      env <- lift $ interpretDeclaration True env decl -- Interpretation.
      -- Purge used non-duplicable values.
      let fv = freevar decl
      IntSet.fold (\x rec -> do
          (gamma, env, cset) <- rec
          case IntMap.lookup x gamma of
            Just (TypeScheme _ _ _ (TypeAnnot f _)) -> do
              v <- runTyper $ getFlagValue f
              case v of
                Zero -> return (IntMap.delete x gamma, IntMap.delete x env, cset)
                _ -> return (gamma, env, cset)
            Nothing -> return (gamma, env, cset)
        ) (return (gamma, env, cset)) fv
    ) (return (typemap inter, valuation inter, constraints inter)) declarations
  -- Update the state.
  modify $ \inter -> inter {
      environment = Translate.environment state,
      typemap = gamma,
      valuation = env,
      constraints = cset
    }


-- | Run the interactive mode, parsing the input commands and sending information back accordingly.
-- Two kind of commands are interpreted:
--
-- * Proto-Quipper code: anything that contains the string \";;\". Multi-line commands are permitted.
--   Anything that is part of a module implementation can be passed as a command: import statements,
--   type definitions, and top-level declarations.
--
-- * Context commands: any command starting with the prefix \":\". These commands occupy a single
--   line, and give information about the current state of the machine. Typical commands are \":context\",
--   which lists the variables currently in scope, and \":display\", which displays the top-level
--   circuit (inaccessible otherwise).
--
runInteractive :: [String] -> Interactive ()
runInteractive buffer = do
  -- Wait for user input.
  l <- case buffer of
      [] -> runCore $ prompt "# "
      _ -> runCore $ prompt "  "

  -- Check the command.
  case l of
    -- Quit the interactive mode.
    Nothing -> do
      runIO $ putStrLn ""
      runIO $ hFlush stdout
      exit

    Just l ->
      if string_ends_with ";;" l then do
        -- Add the command to the history.
        runCore $ addHistory $ List.foldl (\r c -> c ++ "\n" ++ r) l buffer
        -- Process the 'module'.
        let doProcessModule = do
              tokens <- runIO $ mylex unknownFile $ B.pack
                  (List.map (toEnum . fromEnum) $ List.foldl (\r l -> l ++ "\n" ++ r) "" (l:buffer))
              let program = parse tokens
              runCore $ changeOptions (\options -> options { displayToplevelTypes = True })
              runCommand program
        -- Execute the computation in a safe context.
        doProcessModule `CM.catch` (\(e :: SomeException) -> do
            runIO $ hPutStrLn stderr $ show e
            return ())
        -- Resume the command input
        runInteractive []

      else if buffer == [] && List.isPrefixOf ":" l then do
        runCore $ addHistory l
        let w = words l
            cmd = List.head w
            args = List.tail w
        case prefix_of cmd (List.map fst commands) of
          [] -> do
            runIO $ putStrLn $ "Unknown command: '" ++ cmd ++ "' -- Try :help for more information"
            runInteractive []

          [":help"] -> do
            w <- return $ (List.maximum $ List.map (List.length . fst) commands) + 5
            List.foldl (\rec (c, descr) -> do
                rec
                runIO $ putStrLn $ c ++ (List.replicate (w - List.length c) ' ') ++ descr
              ) (return ()) commands
            runInteractive []

          [":exit"] -> exit

          [":context"] -> do
            typemap <- gets typemap
            IntMap.foldWithKey (\x (TypeScheme _ _ _ (TypeAnnot f b)) rec -> do
                rec
                v <- runTyper $ getFlagValue f
                t <- runTyper $ printType (TypeAnnot f b)
                name <- runCore $ variableName x
                runIO $ putStr "~ "
                case v of
                  Zero -> runCore $ putStrC Red name
                  One -> runCore $ putStrC Yellow name
                  Unknown -> runCore $ putStrC Blue name
                runIO $ putStrLn $ " : " ++ t
              ) (return ()) typemap
            runInteractive []

          [":display"] -> do
            circuits <- lift $ gets circuits
            let circ = List.head circuits
            runIO $ putStrLn (pprint circ ++ " : circ((), _)")
            runInteractive []

          [":type"] -> do
            if args == [] then runIO $ putStrLn "Error: the command ':type' expects one argument"
            else do
              let term = unwords args
              let doPrintType = do
                    tokens <- runIO $ mylex unknownFile $ B.pack (List.map (toEnum . fromEnum) (term ++ ";;"))
                    let program = parse tokens
                    case S.body program of
                      (S.DExpr info value):_ -> do
                        -- Translation of the expression into internal syntax.
                        state <- getTranslateState
                        (value, _) <- runCore $ runStateT (translateExpression value) state
                        -- Free variables of the new expression.
                        let fve = freevar value
                        a @ (TypeAnnot n _) <- runCore newType
                        -- Type e. The constraints from the context are added for the unification.
                        gamma <- gets typemap
                        (gammaE, _) <- runTyper $ subContext fve gamma
                        (value, cset) <- runTyper $ constraintTyping gammaE value [a]
                        topcset <- gets constraints
                        cset <- runTyper $ breakConstraintSet cset
                        cset' <- runTyper $ unify (cset <> topcset)
                        a' <- runTyper $ resolveType a
                        inferred <- runTyper $ printType a'
                        -- Display the type
                        runIO $ putStrLn $ "-: " ++ inferred
                      _ -> runIO $ putStrLn "-: ()"

              -- Run the computation in a guarded environment.
              doPrintType `CM.catch` (\(e :: SomeException) -> do
                  runIO $ hPutStrLn stderr $ show e
                  return ())

            runInteractive []

          [":path"] -> do
            runCore $ changeOptions $ \options -> options {
                includeDirs = (includeDirs options) ++ [unwords args] }
            runInteractive []

          [":value"] -> do
            List.foldl (\rec name -> do
                rec
                variables <- gets (Environment.variables . environment)
                case Map.lookup name variables of
                  Just (Global x) -> do
                    context <- lift $ gets Interpreter.context
                    case IntMap.lookup x context of
                      Just v -> runIO $ putStrLn $ "val " ++ name ++ "=" ++ pprint v
                      Nothing -> fail $ "Interactive:runInteractive: undefined global variable: " ++ show x

                  Just (Local x) -> do
                    env <- gets valuation
                    case IntMap.lookup x env of
                      Just v -> runIO $ putStrLn $ "val " ++ name ++ "=" ++ pprint v
                      Nothing -> fail $ "Interactive:runInteractive: undefined variable: " ++ show x

                  Nothing -> runIO $ putStrLn $ "Unknown variable " ++ name
              ) (return ()) args

            runInteractive []

          [":fulltype"] -> do
            if args == [] then runIO $ putStrLn "Error: the command ':fulltype' expects one argument"
            else do
              let term = unwords args
              let doPrintType = do
                    tokens <- runIO $ mylex unknownFile $ B.pack (List.map (toEnum . fromEnum) (term ++ ";;"))
                    let program = parse tokens
                    case S.body program of
                      (S.DExpr info value):_ -> do
                        -- Translation of the expression into internal syntax.
                        state <- getTranslateState
                        (value, _) <- runCore $ runStateT (translateExpression value) state
                        -- Free variables of the new expression.
                        let fve = freevar value
                        a @ (TypeAnnot n _) <- runCore newType
                        -- Limit for polymorphic types.
                        limtype <- runCore freshType
                        limflag <- runCore freshFlag
                        -- Type e. The constraints from the context are added for the unification.
                        gamma <- gets typemap
                        (gammaE, _) <- runTyper $ subContext fve gamma
                        (value, cset) <- runTyper $ constraintTyping gammaE value [a]
                        topcset <- gets constraints
                        cset <- runTyper $ breakConstraintSet cset
                        cset' <- runTyper $ unify (cset <> topcset)
                        a' <- runTyper $ resolveType a
                        -- Limit for polymorphic types.
                        endtype <- runCore freshType
                        endflag <- runCore freshFlag
                        -- Simplify the constraint set
                        (TypeScheme ff fv cset a @ (TypeAnnot n _)) <- runTyper $ makePolymorphicType a' cset' (\f -> limflag <= f && f < endflag, \v -> limtype <= v && v < endtype)
                        -- Display the type
                        pVar <- runTyper $ displayTypeVar fv
                        pFlag <- runTyper $ displayRefFlag (n:ff)
                        pUser <- runCore $ displayUserType

                        let inferred = genprint Inf [pFlag, pVar, pUser] a
                            constraints = genprint Inf [pFlag, pVar, pUser] cset

                        runIO $ putStrLn $ "-: " ++ inferred ++ " with\n" ++ constraints
                      _ -> runIO $ putStrLn "-: ()"

              -- Run the computation in a guarded environment.
              doPrintType `CM.catch` (\(e :: SomeException) -> do
                  runIO $ hPutStrLn stderr $ show e
                  return ())

            runInteractive []

          _ -> do
            runIO $ putStrLn $ "Ambiguous command: '" ++ l ++ "' -- Try :help for more information"
            runInteractive []

        else runInteractive $ l:buffer


-- | A list of valid context commands, associated with their descriptions. The commands are (for now):
--
-- * :help - display the list of commands.
--
-- * :context - list the variables in scope, and their type. Depending on the operating system, the
--   duplicable variables may be printed in yellow, the non duplicable in red.
--
-- * :exit - quit the interactive mode. Before quitting, a check is performed to ensure that no
--   non-duplicable object is discarded.
--
-- * :display - display the top-level circuit (in visual mode), which is otherwise inaccessible.
--
commands :: [(String, String)]
commands = [
  (":help", "Show the list of commands"),
  (":exit", "Quit the interactive mode"),
  (":path", "Add a directory to the current module path"),
  (":type", "Show the simplified type of an expression"),
  (":fulltype", "Show the detailed type of an expression"),
  (":context", "List the currently declared variables"),
  (":display", "Display the current toplevel circuit"),
  (":value", "Display the value of one or more variables, without consuming it")
  ]


-- | Quit the interactive mode. Before quitting, a check is performed to ensure that no non
-- duplicable object is discarded.
exit :: Interactive ()
exit = do
  typemap <- gets typemap
  -- List all the non-duplicable variables.
  nodup <- IntMap.foldWithKey (\x (TypeScheme _ _ _ (TypeAnnot f _)) rec -> do
      nodup <- rec
      v <- runTyper $ getFlagValue f
      case v of
        Zero -> do
          n <- runCore $ variableName x
          return $ n:nodup
        _ -> return nodup
    ) (return []) typemap

  case nodup of
    [] -> return ()
    _ -> do
      runIO $ putStrLn "Warning: the following variables are not duplicable and will be discarded:"
      runIO $ putStr $ "~"
      List.foldl (\rec n -> do
          rec
          runIO $ putStr "  "
          runCore $ putStrC Red n
        ) (return ()) nodup
      runIO $ putStrLn ""


-- | Launch the execution of the interactive mode.
launchInteractive :: Core ()
launchInteractive = do
  interactiveState <- Interactive.init
  -- Core.
  typerState <- Typer.init ["Builtins"]
  (_, _) <- runStateT (do
      -- Typer.
      interpreterState <- Interpreter.init ["Builtins"]
      (_, _) <- runStateT (do
          -- Interpreter.
          (_, _) <- runStateT (runInteractive []) interactiveState
          return ()
        ) interpreterState
      return ()
    ) typerState
  return ()

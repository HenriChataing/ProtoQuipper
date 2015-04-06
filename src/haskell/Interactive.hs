-- | This module implements the interactive mode of Proto-Quipper.
module Interactive where

import Options
import Classes
import Console
import Utils
import Driver

import Parsing.Lexer
import Parsing.Parser
import Parsing.Location
import qualified Parsing.Syntax as S

import Core.Syntax
import Core.Translate
import Core.Environment as Environment (variables, Trace (..))

import Typer.TypingContext
import Typer.Subtyping
import qualified Typer.TypeInference (filter)
import Typer.TypeInference

import Interpreter.Circuits
import Interpreter.Values (Value)

import Monad.Error
import Monad.Core (Core, getOptions, variableName)
import Monad.Typer (Typer, FlagValue (..), getFlagValue)
import Monad.Interpreter (Interpreter)
import qualified Monad.Interpreter as Interpreter (runCore, runTyper)

import System.IO

import Control.Exception
import qualified Data.List as List
import qualified Data.Map as Map
import Data.IntMap as IntMap
import qualified Data.ByteString.Lazy as B

import Control.Monad.Trans.State
import Control.Monad.Trans


-- | The interactive mode runs in a specific monad, on top of the interpreter monad.
data InteractiveState = InteractiveState {
  environment :: Environment,
  typemap :: IntMap TypeScheme,
  valuation :: IntMap Value
}

type Interactive = StateT InteractiveState Interpreter


runCore :: Core a -> Interactive a
runCore computation = lift $ Interpreter.runCore computation

runTyper :: Typer a -> Interactive a
runTyper computation = lift $ Interpreter.runTyper computation

runIO :: IO a -> Interactive a
runIO computation = lift $ Interpreter.runCore $ lift computation


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
  depends <- buildSetDependencies (includeDirs options) moduleNames
  -- Process the modules. If a module was explicitly imported, then it is re-processed.
  List.foldl (\rec p -> do
      ctx <- rec
      let mopts = ModuleOptions { toplevel = False, disp_decls = False }

      -- If the module has been explicitly included, re-process it
      if List.elem (S.moduleName p) moduleNames then do
        -- Re-process
        m <- process_module (opts, mopts) p
        -- Import
        return $ ctx { labelling = M.environment m <+> labelling ctx }
      else do
        -- Check whether the module has already been imported or not
        imported <- get_context >>= return . modules
        -- If needed, process the module, in any case return the module contents
        case List.lookup (S.moduleName p) imported of
          Just m -> do
              -- The module already exists
              return ()
          Nothing -> do
              -- Process the module
              _ <- process_module (opts, mopts) p
              return ()
        return ctx) (return ctx) depends
  return ctx


-- | Process a user command. Since the command is like a module implementation, it is dealt with the
-- same way. The only exception concerns import declarations, which are handled specifically by the
-- function 'Interactive.importModules'.
runCommand :: S.Program -> Interactive ()
runCommand prog ctx = do
  -- Import the modules.
  importModules (S.imports prog)
  -- Interpret all the declarations.
  ctx <- List.foldl (\rec decl -> do
      ctx <- rec
      (ctx, _) <- process_declaration opts prog ctx decl
      return ctx) (return ctx) $ S.body prog
  -- Return.
  return ctx


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
        addHistory $ List.foldl (\r c -> c ++ "\n" ++ r) l buffer

        -- Process the 'module'.
        ctx <- (do
              tokens <- mylex file_unknown $ B.pack (List.map (toEnum . fromEnum) $ List.foldl (\r l -> l ++ "\n" ++ r) "" (l:buffer))
              prog <- return $ parse tokens

              runCommand (opts, ModuleOptions { toplevel = True, disp_decls = True }) prog ctx)
          `catchQ` (\e -> do
              runIO $ hPutStrLn stderr $ show e
              return ctx)

        -- Resume the command input
        runInteractive opts ctx []

        else if buffer == [] && List.isPrefixOf ":" l then do
          addHistory l
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
                    Zero -> runCore $ putStrC Red nm
                    One -> runCore $ putStrC Yellow nm
                    Unknown -> runCore $ putStrC Blue nm
                  runIO $ putStrLn $ " : " ++ t
                ) (return ()) typemap
              runInteractive []

            [":display"] -> do
              circ <- lift $ gets (List.head . circuits)
              runIO $ putStrLn (pprint circ ++ " : circ((), _)")
              runInteractive []

            [":type"] -> do
              if args == [] then runIO $ putStrLn "Error: the command ':type' expects one argument"
              else do
                let term = unwords args
                let doPrintType = do
                      tokens <- mylex file_unknown $ B.pack (List.map (toEnum . fromEnum) (term ++ ";;"))
                      p <- return $ parse tokens
                      case S.body p of
                        [] -> runIO $ putStrLn "-: ()"
                        _ -> do
                          S.DExpr e <- return $ List.head (S.body p)

                          -- Translation of the expression into internal syntax.
                          e' <- translateExpression e $ labelling ctx

                          -- Free variables of the new expression
                          fve <- return $ free_var e'
                          a@(TypeAnnot n _) <- new_type

                          -- Type e. The constraints from the context are added for the unification.
                          gamma <- return $ typing ctx
                          (gamma_e, _) <- subContext fve gamma
                          cset <- constraintTyping gamma_e e' [a] >>= break_composite
                          cset' <- unify (exact opts) (cset <> constraints ctx)
                          inferred <- resolveType a >>= printType

                          -- Display the type
                          runIO $ putStrLn $ "-: " ++ inferred

                -- Run the computation in a guarded environment.
                doPrintType `catchQ` (\e -> do
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
                  variables <- gets (Namespace.variables . namespace)
                  case Map.lookup name variables of
                    Just (Global x) -> do
                      context <- lift $ gets Interpreter.context
                      case IntMap.lookup x context of
                        Just v -> runIO $ putStrLn $ "val " ++ name ++ "=" ++ pprint v
                        Nothing -> fail $ "INteractive:runInteractive: undefined global variable: " ++ show x

                    Just (Local x) -> do
                      env <- gets valuation
                      case IntMap.lookup x env of
                        Just v -> runIO $ putStrLn $ "val " ++ name ++ "=" ++ pprint v
                        Nothing -> fail $ "Interactive:runInteractive: undefined variable: " ++ show x

                    Nothing -> runIO $ putStrLn $ "Unknown variable " ++ name
                ) (return ()) args

              runInteractive opts ctx []

            [":fulltype"] -> do
              if args == [] then runIO $ putStrLn "Error: the command ':fulltype' expects one argument"
              else do
                let term = unwords args
                let doPrintType = do
                      tokens <- mylex file_unknown $ B.pack (List.map (toEnum . fromEnum) (term ++ ";;"))
                      p <- return $ parse tokens
                      case S.body p of
                        [] -> runIO $ putStrLn "-: ()"
                        _ -> do
                          S.DExpr e <- return $ List.head (S.body p)
                          -- Translation of the expression into internal syntax.
                          e' <- translateExpression e $ labelling ctx
                          -- Free variables of the new expression
                          fve <- return $ free_var e'
                          a@(TypeAnnot n _) <- new_type
                          -- Type e. The constraints from the context are added for the unification.
                          limtype <- get_context >>= return . type_id
                          limflag <- get_context >>= return . flag_id

                          gamma <- return $ typing ctx
                          (gamma_e, _) <- subContext fve gamma
                          cset <- constraintTyping gamma_e e' [a] >>= break_composite
                          cset' <- unify (exact opts) (cset <> constraints ctx)
                          inferred <- resolveType a

                          endtype <- get_context >>= return . type_id
                          endflag <- get_context >>= return . flag_id

                          -- Simplify the constraint set
                          (TypeScheme ff fv cset a@(TypeAnnot n _)) <- makePolymorphicType inferred cset' (\f -> limflag <= f && f < endflag, \v -> limtype <= v && v < endtype)

                          -- Display the type
                          fvar <- display_typvar fv
                          fflag <- displayRefFlag (n:ff)
                          fuser <- displayUserType

                          pinf <- return $ genprint Inf [fflag, fvar, fuser] a
                          pcset <- return $ genprint Inf [fflag, fvar, fuser] cset

                          runIO $ putStrLn $ "-: " ++ pinf ++ " with\n" ++ pcset

                -- Run the computation in a guarded environment.
                doPrintType `catch` (\e -> do
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

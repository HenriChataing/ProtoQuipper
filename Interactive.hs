-- | This module defines all the functions needed to run the interactive mode.
module Interactive where

import Options
import Classes

import Parsing.Lexer
import Parsing.Parser
import Parsing.Localizing
import qualified Parsing.Syntax as S

import Typing.CoreSyntax
import Typing.TypingContext
import Typing.Driver
import Typing.TransSyntax
import qualified Typing.TypeInference (filter)
import Typing.TypeInference

import Interpret.Circuits

import Monad.QuipperError
import Monad.QpState
import Monad.Modules

import System.IO
import System.Console.Readline

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.IntMap as IMap



-- | Import a module and its dependencies in the current context.
import_modules :: Options -> [String] -> ExtensiveContext -> QpState ExtensiveContext
import_modules opts mnames ctx = do 
  -- Build the dependencies (with a dummy module that is removed immediately)
  deps <- build_dependencies (includes opts) S.dummy_program { S.imports = mnames }
  deps <- return $ List.init deps

  -- Process everything, finishing by the main file
  ctx <- List.foldl (\rec p -> do
                ctx <- rec
                mopts <- return $ MOptions { toplevel = False, disp_decls = False }
                -- Check whether the module has already been imported or not
                imported <- get_context >>= return . modules
                case List.lookup (S.module_name p) imported of
                  -- Do nothing
                  Just m ->
                      return ctx
                  Nothing -> do
                      process_module (opts, mopts) p
                      -- Move the module internally onto the modules stack
                      qst <- get_context
                      set_context $ qst { modules = (S.module_name p, cmodule qst):(modules qst) }
                      -- Import the declarations in the extensive context
                      cm <- return $ cmodule qst
                      ctx <- return $ ctx { typing = IMap.union (global_types cm) (typing ctx),
                                            label = Map.union (global_ids cm) (label ctx),
                                            environment = IMap.union (global_vars cm) (environment ctx) }
                      return ctx) (return ctx) deps
  set_file file_unknown
  return ctx




-- | Process the input commands.
run_command :: (Options, MOptions) -> S.Program -> ExtensiveContext -> QpState ExtensiveContext
run_command opts prog ctx = do
  -- Import the modules
  ctx <- import_modules (fst opts) (S.imports prog) ctx

  -- translate the module header : type declarations
  dcons <- import_typedefs (workWithProto $ fst opts) $ S.typedefs prog
  define_user_subtyping $ S.typedefs prog
  define_user_properties $ S.typedefs prog
 
  -- Interpret all the declarations
  ctx <- List.foldl (\rec decl -> do
                       ctx <- rec
                       process_declaration opts prog ctx decl) (return $ ctx { label = Map.union dcons $ label ctx }) $ S.body prog
  -- Return
  return ctx



-- | Run the interactive mode, parsing the intput commands and sending information back
-- accordingly. It keeps track of an extensive context that cumulates labelling, evaluation, typing, constraints.
-- The second string argument is the buffer of the command : the commnad is only flushed and interpreted when a ;;
-- character is read, else the lines are pushed to this buffer.
run_interactive :: Options -> ExtensiveContext -> [String] -> QpState ()
run_interactive opts ctx buffer = do
  -- Wait for user input
  l <- case buffer of
         [] -> liftIO $ readline "# "
         _ -> liftIO $ readline "  "

  -- Check the command
  case l of
    Nothing -> do 
        -- Quit the interactive mode
        liftIO $ putStrLn ""
        liftIO $ hFlush stdout
        exit ctx

    Just l ->
        if List.isSuffixOf ";;" l then do
          -- Add the command to the history
          liftIO $ addHistory $ List.foldl (\r c -> c ++ "\n" ++ r) l buffer

          tokens <- liftIO $ mylex $ List.foldl (\r l -> l ++ "\n" ++ r) "" (l:buffer)
          prog <- return $ parse tokens
          -- Process the 'module'
          ctx <- (run_command (opts, MOptions { toplevel = True, disp_decls = True }) prog ctx
                 )`catchQ` (\e -> do
                              liftIO $ putStrLn $ show e
                              return ctx)

          -- Resume the command input
          run_interactive opts ctx []

        else if buffer == [] && List.isPrefixOf ":" l then
          case prefix_of l (List.map fst commands) of
            [] -> do
                liftIO $ putStrLn $ "Unknown command: '" ++ l ++ "' -- Try :help for more information"
                run_interactive opts ctx []

            [":help"] -> do
                List.foldl (\rec (c, descr) -> do
                              rec
                              liftIO $ putStrLn $ c ++ " -- " ++ descr) (return ()) commands
                run_interactive opts ctx []
                
            [":exit"] -> do
                exit ctx  

            [":ctx"] -> do
                IMap.foldWithKey (\x a rec -> do 
                                    rec
                                    n <- variable_name x
                                    t <- pprint_type_noref a
                                    liftIO $ putStrLn $ "~" ++ n ++ " : " ++ t) (return ()) (typing ctx)
                run_interactive opts ctx []

            [":used"] -> do
                List.foldl (\rec x -> do
                              rec
                              n <- variable_name x
                              liftIO $ putStrLn $ "~" ++ n) (return ()) (used ctx)
                run_interactive opts ctx []

            [":display"] -> do
                c <- get_context >>= return . List.head . circuits
                pc <- return $ pprint c
                liftIO $ putStrLn pc
                run_interactive opts ctx []

            _ -> do
              liftIO $ putStrLn $ "Ambiguous command: '" ++ l ++ "' -- Try :help for more information"
              run_interactive opts ctx []
     
      else
        run_interactive opts ctx (l:buffer) 
 

-- | List of valid commands, associated to their description.
commands :: [(String, String)]
commands = [
  (":help", "Display the list of commands"),
  (":ctx", "List the variables of the current context"),
  (":used", "List the variables that have already been used"),
  (":exit", "Quit the interactive mode"),
  (":display", "Display the toplevel circuit") ]



-- | Quits the interactive mode. As it tries quitting, it checks
-- the variables that are dropped are indeed duplicable.
exit :: ExtensiveContext -> QpState ()
exit ctx = do
  (_, delta) <- sub_context (used ctx) (typing ctx)
  fconstraints <- force_duplicable_context delta >>= Typing.TypeInference.filter
  _ <- unify True (fconstraints <> constraints ctx)
  return ()

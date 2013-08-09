-- | This module defines all the functions needed to run the interactive mode.
module Interactive where

import Options

import Parsing.Lexer
import Parsing.Parser
import qualified Parsing.Syntax as S

import Typing.Driver
import Typing.TransSyntax

import Monad.QuipperError
import Monad.QpState
import Monad.Modules

import System.IO

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
  List.foldl (\rec p -> do
                ctx <- rec
                mopts <- return $ MOptions { toplevel = List.elem (S.module_name p) mnames, disp_decls = False }
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
  l <- liftIO getLine
  if List.isSuffixOf ";;" l then do
    tokens <- liftIO $ mylex $ List.foldl (\r l -> l ++ "\n" ++ r) "" (l:buffer)
    prog <- return $ parse tokens
    -- Process the 'module'
    ctx <- (run_command (opts, MOptions { toplevel = True, disp_decls = True }) prog ctx
           )`catchQ` (\e -> do
                        liftIO $ putStrLn $ show e
                        return ctx)

    -- Resume the command input
    liftIO $ putStr "# "
    liftIO $ hFlush stdout
    run_interactive opts ctx []
  else if buffer == [] && List.isPrefixOf ":" l then
    if l == ":exit" then do
      -- NEED TO CHECK NO DISCARDING OF NON DUP VARIABLES
      return ()
    else do

      case l of
        ":ctx" ->
            IMap.foldWithKey (\x a rec -> do 
                              rec
                              n <- variable_name x
                              t <- pprint_type_noref a
                              liftIO $ putStrLn $ "~" ++ n ++ " : " ++ t) (return ()) (typing ctx)
        ":used" ->
            List.foldl (\rec x -> do
                        rec
                        n <- variable_name x
                        liftIO $ putStrLn $ "~" ++ n) (return ()) (used ctx)

        _ -> return ()

      -- Resume the command input
      liftIO $ putStr "# "
      liftIO $ hFlush stdout
      run_interactive opts ctx []

  else
    run_interactive opts ctx (l:buffer) 
  
 

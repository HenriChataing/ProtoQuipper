-- | This module provides an interface to the type inference and unification algorithms. It introduces functions to
-- parse and process modules, and to deal with module dependencies.
module Typing.Driver where

import Classes
import Utils
import Options
import Builtins

import Parsing.Lexer
import qualified Parsing.Parser as P
import qualified Parsing.IParser as IP
import Parsing.Location (clear_location, extent_unknown)
import Parsing.Syntax (RecFlag(..))
import qualified Parsing.Syntax as S
import Parsing.Printer

import Typing.CoreSyntax
import Typing.TransSyntax

import Interpret.Interpret
import Interpret.Values
import Interpret.IRExport
import Interpret.Circuits

import Typing.Ordering
import Typing.Subtyping
import Typing.TypeInference
import Typing.TypingContext
import Typing.TransSyntax

import Monad.QpState
import Monad.Modules
import Monad.QuipperError

import System.Directory
import System.FilePath.Posix

import Control.Exception
import Data.List as List
import Data.Map as Map
import Data.IntMap as IMap
import Data.Char as Char


-- | Lex and parse the module implementation file at the given filepath.
lex_and_parse_implementation :: FilePath -> QpState S.Program
lex_and_parse_implementation file = do
  contents <- liftIO $ readFile file
  tokens <- mylex file contents
  mod <- return $ module_of_file file
  return $ (P.parse tokens) { S.module_name = mod, S.filepath = file, S.interface = Nothing }


-- | Lex and parse the interface file at the given filepath.
lex_and_parse_interface :: FilePath -> QpState S.Interface
lex_and_parse_interface file = do
  contents <- liftIO $ readFile file
  tokens <- mylex file contents
  mod <- return $ module_of_file file
  return $ IP.parse tokens


-- | Find the implementation of a module in a given directory.
-- The name of the code file is expected to be /dir/\//module/./ext/,
-- where /dir/ is the directory, /module/ is the name of the module (with
-- the first letter changed to lower case), and /ext/ the extension, which can be either @.qp@ (implementation)
-- or @.qpi@ (interface). \'/dir/\' is taken in the provided list of directories.
-- If several implementations are found, an error is raised.
find_in_directories :: String       -- ^ Module name.
                    -> [FilePath]   -- ^ List of directories.
                    -> String       -- ^ Extension.
                    -> QpState (Maybe FilePath)
find_in_directories mod@(initial:rest) directories extension = do
  mfile <- return $ (Char.toLower initial):(rest ++ extension)
  existing <- List.foldl (\rec d -> do
                            r <- rec
                            nexttry <- return $ combine d mfile
                            exists <- liftIO $ doesFileExist nexttry
                            if exists then
                              return (nexttry:r)
                            else
                              return r) (return []) directories
  case existing of
    [] ->
        return Nothing

    [path] ->
        -- OK
        return $ Just path

    (m1:m2:_) ->
        -- Several implementations found
        throwQ $ DuplicateImplementation mod m1 m2

find_in_directories "" directories extension = do
  throw $ ProgramError "find_in_directories: empty module name"

-- | Specifically look for the implementation of a module.
-- Since an implementation is expected, the function fails if no matching
-- file is found (and also if more than one exists).
find_implementation_in_directories :: String -> [FilePath] -> QpState FilePath
find_implementation_in_directories mod directories = do
  f <- find_in_directories mod directories ".qp"
  case f of
    Just f ->
        return f 

    Nothing ->
        -- The module doesn't exist
        throwQ $ NonExistingModule mod


-- | Specifically look for the interface of a module.
-- Since the interface file is optional, so is the return value.
find_interface_in_directories :: String -> [FilePath] -> QpState (Maybe FilePath)
find_interface_in_directories mod directories =
  find_in_directories mod directories ".qpi"



-- | Recursively explore the dependencies of the program. This function returns
-- a map linking the modules to their parsed implementations, and a map corresponding
-- to the dependency graph.
-- It proceeds to sort the dependencies topologically using an in-depth exploration of the graph.
-- Note that the return list is reversed, with the \'oldest\' module first.
-- During the exploration, if a module is visited that had already been explored but not yet pushed on
-- the sorted list, an error is generated (cyclic dependencies).
explore_dependencies :: [FilePath]            -- ^ List of directories.
                     -> S.Program             -- ^ Current module.
                     -> [String]              -- ^ The list of explored modules.
                     -> [S.Program]           -- ^ The dependencies that have already been sorted.
                     -> QpState ([S.Program], [String])
explore_dependencies dirs prog explored sorted = do
  -- Mark the module as explored
  explored <- return $ (S.module_name prog):explored
  -- Sort the dependencies
  (s,ex) <- List.foldl (\rec m -> do
                           (sorted, exp) <- rec
                           case (List.elem m exp, List.find (\p -> S.module_name p == m) sorted) of
                             -- Ok
                             (True, Just _) ->
                                 return (sorted, exp)

                             -- Not ok
                             (True, Nothing) -> do
                                 -- The module has already been visited : cyclic dependency
                                 -- Build the loop : by removing the already sorted modules,
                                 -- and spliting the explored list at the first visit of this module.
                                 flush_logs
                                 inloop <- return $ explored List.\\ (List.map S.module_name sorted)
                                 (loop, _) <- return $ List.span (\m' -> m' /= m) inloop

                                 throwQ $ CyclicDependencies m (List.reverse (m:loop))

                             -- Explore
                             _ -> do
                                 file <- find_implementation_in_directories m dirs
                                 inter <- find_interface_in_directories m dirs
                                 p <- lex_and_parse_implementation file
                                 p <- case inter of
                                        Just f -> do
                                            interface <- lex_and_parse_interface f
                                            return $ p { S.interface = Just interface }
                                        Nothing -> return p

                                 explore_dependencies dirs p exp sorted) (return (sorted, explored)) (S.imports prog)
  -- Push the module on top of the list : after its dependencies
  return (prog:s, ex)


-- | Sort the dependencies of file in a topological fashion.
-- The program argument is the main program, on which Proto-Quipper has been called. The return value
-- is a list of the dependencies, with the properties:
--
--     * each module may only appear once;
--
--     * the dependencies of each module are placed before it in the sorted list; and
--
--     * (as a corollary) the main module is placed last.
--
build_dependencies :: [FilePath]          -- ^ List of directories.
                   -> S.Program           -- ^ Main module.
                   -> QpState [S.Program] -- ^ Returns the total list of dependencies, sorted in a topological fashion.
build_dependencies dirs main = do
  (deps, _) <- explore_dependencies dirs main [] []
  return $ List.reverse deps





-- | The type of /extensive contexts/, which are used during the processing of top-level declarations.
data ExtensiveContext = Context {
  labelling :: LabellingContext,        -- ^ A labelling context.
  typing :: TypingContext,              -- ^ A typing context.
  environment :: Environment,           -- ^ An evaluation context.
  constraints :: ConstraintSet          -- ^ An atomic constraint set that accumulates the constraints of all the top-level expressions.
}


-- | A type for processing options that are specific to modules (as opposed to program options, which affect
-- the whole program).
data MOptions = MOptions {
  toplevel :: Bool,               -- ^ Is the module at top level (in a sense: was it given as argument of the program).
  disp_decls :: Bool              -- ^ Display the variable declarations or not.
}



-- | Process a list of top-level declarations (corresponding to either commands in interactive mode, or
-- the body of a module). The arguments include the vector of command options, the current module,
-- an extensive context, and a declaration.
process_declaration :: (Options, MOptions)       -- ^ The command line and module options combined.
                    -> S.Program                 -- ^ The current module.
                    -> ExtensiveContext          -- ^ The context.
                    -> S.Declaration             -- ^ The declaration to process.
                    -> QpState ExtensiveContext  -- ^ Returns the updated context.


-- TYPE SYNONYMS
process_declaration (opts, mopts) prog ctx (S.DSyn typesyn) = do
  label <- import_typesyn typesyn $ labelling ctx
  return $ ctx { labelling = label }


-- DATA TYPE BLOCKS
process_declaration (opts, mopts) prog ctx (S.DTypes typedefs) = do
  label <- import_typedefs typedefs $ labelling ctx
  return $ ctx { labelling = label }


-- EXPRESSIONS
process_declaration (opts, mopts) prog ctx (S.DExpr e) = do
  -- Translation of the expression into internal syntax.
  e' <- translate_expression e $ labelling ctx

  -- Free variables of the new expression
  fve <- return $ free_var e'
  a@(TBang n _) <- new_type

  -- ALL TOP-LEVEL EXPRESSIONS MUST BE DUPLICABLE :
  ex <- case e' of
          ELocated _ ex -> return ex
          _ -> return $ extent_unknown
  set_flag n no_info { expression = e',
                       loc = ex }

  -- Type e. The constraints from the context are added for the unification.
  gamma <- return $ typing ctx
  (gamma_e, _) <- sub_context fve gamma
  cset <- constraint_typing gamma_e e' [a] >>= break_composite True
  cset' <- unify (not $ approximations opts) (cset <> constraints ctx)
  inferred <- map_type a >>= pprint_type_noref

  -- Resolve the constraints (BECAUSE MAP_TYPE CAN CHANGE THE FLAGS)
  fc'' <- unify_flags $ snd cset'
  cset' <- return (fst cset', fc'')

  -- Apply the substitution produced by the unification to the context gamma
  gamma <- IMap.foldWithKey (\x a rec -> do
                               m <- rec
                               a' <- map_typescheme a
                               return $ IMap.insert x a' m) (return IMap.empty) gamma

  -- If interpretation, interpret, and display the result
  if runInterpret opts && toplevel mopts then do
    v <- interpret (environment ctx) e'
    pv <- pprint_value_noref v
    case (v, circuitFormat opts) of
      (VCirc _ c _, "ir") -> do
          irdoc <- return $ export_to_IR c
          liftIO $ putStrLn irdoc
      (VCirc _ c _, "visual") ->
          liftIO $ putStrLn (pprint c ++ " : " ++ inferred)
      _ ->
          liftIO $ putStrLn (pv ++ " : " ++ inferred) 
  else if toplevel mopts then
    liftIO $ putStrLn ("-: "  ++ inferred)
  else
    return ()

  -- Remove the used AND non duplicable variables from the context
  IMap.foldWithKey (\x a rec -> do
                      ctx <- rec
                      let (TForall _ _ _ (TBang f _)) = a
                      v <- flag_value f
 
                      case (List.elem x fve, v) of
                        (True, Zero) -> do
                            n <- variable_name x
                            return $ ctx { labelling = (labelling ctx) { l_variables = Map.delete n $ l_variables (labelling ctx) },
                                           typing = IMap.delete x $ typing ctx,
                                           environment = IMap.delete x $ environment ctx }

                        _ ->
                            return ctx) (return $ ctx { typing = gamma,
                                                        constraints = cset' }) gamma


-- LET BINDING
process_declaration (opts, mopts) prog ctx (S.DLet recflag p e) = do
  -- Translate pattern and expression into the internal syntax
  (p', label') <- translate_pattern p $ labelling ctx
  e' <- case recflag of
          Recursive -> translate_expression e $ (labelling ctx) { l_variables = label' }
          Nonrecursive -> translate_expression e $ labelling ctx
  fve <- return $ free_var e'

  -- Export the variables of the pattern
  p' <- with_interface prog (labelling ctx) p'

  -- Give the corresponding sub contexts
  gamma <- return $ typing ctx
  (gamma_e, _) <- sub_context fve gamma

  -- Mark the limit free variables / bound variables used in the typing of t
  limtype <- get_context >>= return . type_id
  limflag <- get_context >>= return . flag_id
  -- Create the type of the pattern
  (a, gamma_p, csetp) <- Typing.TypingContext.bind_pattern p'
  -- Type e with this type
  csete <- case recflag of
             Recursive -> do
                 -- Add the bindings of the pattern into gamma_e
                 constraint_typing ((IMap.map typescheme_of_type gamma_p) <+> gamma_e) e' [a]
             Nonrecursive -> do
                 -- If not recursive, do nothing
                 constraint_typing gamma_e e' [a]

  -- Unify the constraints produced by the typing of e (exact unification)
  cs <- break_composite True (csetp <> csete)  -- Break the composite constraints
  csete <- unify True cs                       -- Unify

  -- Apply the substitution produced by the unification of csett to the context gamma
  gamma <- IMap.foldWithKey (\x a rec -> do
                               m <- rec
                               a' <- map_typescheme a
                               return $ IMap.insert x a' m) (return IMap.empty) gamma

  -- Map the types of the pattern
  gamma_p <- IMap.foldWithKey (\x a rec -> do
                                  m <- rec
                                  a' <- map_type a
                                  return $ IMap.insert x a' m) (return IMap.empty) gamma_p

  -- Unify the set again
  fls <- unify_flags $ snd csete
  csete <- return (fst csete, fls)

  -- Last of the free variables of e - to be place after the unification, since
  -- the algorithm produces new variables that also have to be generic.
  endtype <- get_context >>= return . type_id
  endflag <- get_context >>= return . flag_id

  -- -- POLYMORPHISM -- --
  -- If the expression is a VALUE, it can have a generic type.
  gamma_p <- if is_value e' then
    -- Generalize the types of the pattern (= polymorphism)
    IMap.foldWithKey (\x a rec -> do
                        ctx <- rec
                        -- Apply the substitution again
                        --a' <- map_type a
                        a' <- return a
                        -- Clean the constraint set 
                        gena <- make_polymorphic_type a' csete (\f -> limflag <= f && f < endflag, \x -> limtype <= x && x < endtype)

                        -- Update the typing context of u
                        return $ IMap.insert x gena ctx) (return IMap.empty) gamma_p

  -- If the expression is not a value, it has a classical type
  else
    return (IMap.map typescheme_of_type gamma_p)
    

  if disp_decls mopts && toplevel mopts then
    -- Print the types of the pattern p
    IMap.foldWithKey (\x a rec -> do
                        rec
                        nx <- variable_name x
                        case a of
                          TForall _ _ _ a -> do
                              pa <- pprint_type_noref a
                              liftIO $ putStrLn ("val " ++ nx ++ " : " ++ pa)
                        return ()) (return ()) gamma_p
  else
    return ()

  -- Evaluation (even if the module is not top-level, if the general options want it to be evaluated, then so be it)
  ctx <- if runInterpret opts then do
           -- Reduce the argument e1
           v <- interpret (environment ctx) e'
        
           -- Recursive function ?
           env <- case (recflag, v, drop_constraints $ clear_location p') of
                    (Recursive, VFun ev arg body, PVar x) ->
                        let ev' = IMap.insert x (VFun ev' arg body) ev in do
                        Interpret.Interpret.bind_pattern p' (VFun ev' arg body) (environment ctx)

                    _ -> do
                        -- Bind it to the pattern p in the current context
                        Interpret.Interpret.bind_pattern p' v (environment ctx)
           -- End, at last
           return $ ctx { typing = gamma_p <+> gamma,  -- Typing context updated with the bindings of p
                          environment = env }          -- Environment updated with the bindings of p
         else
           return $ ctx { typing = gamma_p <+> gamma } -- Typing context updated with the bindings of p

  -- Remove the variables used by e and non duplicable
  ctx <- IMap.foldWithKey (\x a rec -> do
                      ctx <- rec
                      let (TForall _ _ _ (TBang f _)) = a
                      v <- flag_value f
                      case (List.elem x fve, v) of
                        (True, Zero) -> do
                            n <- variable_name x
                            
                            return $ ctx { labelling = (labelling ctx) { l_variables = Map.update (\v -> let y = case v of
                                                                                                                   LVar y -> y
                                                                                                                   LGlobal y -> y
                                                                                                                   in
                                                                                                         -- The label is removed only if the matching corresponds (to avoid cases like 'let p = p')
                                                                                                         if x == y then Nothing else Just v) n $ l_variables (labelling ctx) },
                                           typing = IMap.delete x $ typing ctx,
                                           environment = IMap.delete x $ environment ctx }
                        _ ->
                            return ctx) (return ctx { labelling = (labelling ctx) { l_variables = label' } }) (typing ctx)
  return ctx


-- | Processes a module. This implies, in turn:
--
-- * processing of the algebraic type definitions.
--
-- * processing of each of the top-level declarations.
-- 
-- * linearity check at the end of the module implementation: checks that no
-- global and non-duplicable variable is discarded.
--
process_module :: (Options, MOptions)  -- ^ Command line options and module options combined.
               -> S.Program            -- ^ Module to process.
               -> QpState Module       -- ^ Return the module contents (variables, data constructors, types).
process_module opts prog = do

  -- Get the module name
  mod <- return $ S.module_name prog
  f <- return $ S.filepath prog

  set_file f

  -- Import the global variables from the dependencies
  (vars, datas, typs) <- global_namespace (S.imports prog)

  -- Save and reset the circuit stack
  ctx <- get_context
  old_stack <- return $ circuits ctx
  set_context $ ctx { circuits = [Circ { qIn = [], gates = [], qOut = [], Interpret.Circuits.qubit_id = 0, unused_ids = [] }] }
 
  -- Interpret all the declarations
  ctx <- List.foldl (\rec decl -> do
                       ctx <- rec
                       process_declaration opts prog ctx decl) (return $ Context { labelling = LblCtx { l_variables = vars, l_datacons = datas, l_types = typs },
                                                                                   typing = IMap.empty,
                                                                                   environment = IMap.empty,
                                                                                   constraints = emptyset }) $ S.body prog

  -- All the variables that haven't been used must be duplicable
  duplicable_context (typing ctx)
  _ <- unify True $ constraints ctx


  -- Import everything to the qstate fields
  qst <- get_context
  set_context $ qst { globals = IMap.union (typing ctx) $ globals qst,
                      values = IMap.union (environment ctx) $ values qst }
                            

  -- Identify the variables created during the processing of the module
  vars <- return $ Map.difference (l_variables $ labelling ctx) vars
  datas <- return $ Map.difference (l_datacons $ labelling ctx) datas
  typs <- return $ Map.difference (l_types $ labelling ctx) typs

  -- Push the definition of the new module to the stack
  newmod <- return $ Mod { m_variables = Map.map unLVar vars,
                           m_datacons = datas,
                           m_types = Map.map unTUser typs }
  ctx <- get_context
  set_context $ ctx { modules = (S.module_name prog, newmod):(modules ctx) }

  -- Return the circuit stack to its original form
  ctx <- get_context
  set_context $ ctx { circuits = old_stack }

  -- Return
  return newmod

  where
      unLVar (LVar id) = id
      unLVar _ = throw $ ProgramError "process_module: leftover global variables"
      
      unTUser (TBang _ (TUser id _)) = id
      unTUser _ = throw $ ProgramError "process_module: expected user type expression"

-- ==================================== --
-- | A function to do everything!
-- In order to sort the dependencies of a list of modules, and to be able to reuse the existing functions for single modules,
-- a dummy module is created that imports all the top-level modules (never to be executed).
do_everything :: Options       -- ^ Command line options.
              -> [FilePath]    -- ^ List of all the modules to process.
              -> QpState ()
do_everything opts files = do
  -- Get the modules' names
  progs <- return $ List.map module_of_file files

  -- Build the dependencies (with a dummy module that is removed immediately)
  deps <- build_dependencies (includes opts) S.dummy_program { S.imports = progs }
  deps <- return $ List.init deps

  -- Process everything, finishing by the main file
  List.foldl (\rec p -> do
                _ <- rec
                mopts <- return $ MOptions { toplevel = List.elem (S.module_name p) progs, disp_decls = False }
                process_module (opts, mopts) p
                return ()) (return ()) deps
-- ===================================== --



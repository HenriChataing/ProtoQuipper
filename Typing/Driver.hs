-- | This module provides an interface to the type inference and unification. It introduces functions to
-- parse and process modules, and deal with module dependencies.
module Typing.Driver where

import Classes
import Utils
import Options
import Builtins

import Parsing.Lexer
import qualified Parsing.Parser as P
import qualified Parsing.IParser as IP
import Parsing.Localizing (clear_location, extent_unknown)
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

import Data.List as List
import Data.Map as Map
import Data.IntMap as IMap
import Data.Char as Char


-- | Lex and parse the file of the given filepath (implementation).
lex_and_parse_implementation :: FilePath -> QpState S.Program
lex_and_parse_implementation file = do
  contents <- liftIO $ readFile file
  tokens <- liftIO $ mylex contents
  mod <- return $ module_of_file file
  return $ (P.parse tokens) { S.module_name = mod, S.filepath = file, S.interface = Nothing }


-- | Lex and parse the file of the given filepath (interface).
lex_and_parse_interface :: FilePath -> QpState S.Interface
lex_and_parse_interface file = do
  contents <- liftIO $ readFile file
  tokens <- liftIO $ mylex contents
  mod <- return $ module_of_file file
  return $ IP.parse tokens


-- | Find the implementation of a module in a given directory
-- The name of the code file is expected to be dir/module.ext,
-- where dir is the directory, module is the name of the module with
-- the first letter put to lower case, and ext the extension, which can be either .qp (implementation)
-- or .qpi (interface). 'dir' is taken in the provided list of directories.
-- If several implementations are found, an error is raised.
find_in_directories :: String -> [FilePath] -> String -> QpState (Maybe FilePath)
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


-- | Specifically look for the implementation of a module
-- Since an implementation is expected, the function fails if no matching
-- file is found.
find_implementation_in_directories :: String -> [FilePath] -> QpState FilePath
find_implementation_in_directories mod directories = do
  f <- find_in_directories mod directories ".qp"
  case f of
    Just f ->
        return f 

    Nothing ->
        -- The module doesn't exist
        throwQ $ NotExistingModule mod


-- | Specifically look for the interface of a module
-- Since the interface file is optional, so is the return value.
find_interface_in_directories :: String -> [FilePath] -> QpState (Maybe FilePath)
find_interface_in_directories mod directories =
  find_in_directories mod directories ".qpi"



-- | Recursively explore the dependencies of the program. It returns
-- a map linking the modules to their parsed implementation, and a map corresponding
-- to the dependency graph.
-- It proceeds to sort topologically the dependencies at the same time, using an in-depth exploration of the graph
-- Note that the return list is reversed, with the 'oldest' module first.
explore_dependencies :: [String] -> S.Program -> [String] -> [S.Program] -> QpState ([S.Program], [String])
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


-- | Sort the dependencies of file in a topological fashion
-- The program argument is the main program, on which quipper has been called. The return value
-- is a list of the dependencies, with the properties :
--      - each module may only appear once.
--      - for each module, every dependent module is placed before in the list.
--      - (as a corollary) the main module is placed last.
build_dependencies :: [String] -> S.Program -> QpState [S.Program]
build_dependencies dirs main = do
  (deps, _) <- explore_dependencies dirs main [] []
  return $ List.reverse deps





-- | Extensive context, used for the processing of declarations.
data ExtensiveContext = Context {
  label :: Map String Int,        -- ^ A labelling map.
  typing :: TypingContext,        -- ^ A typing context.
  environment :: Environment,     -- ^ An evaluation context.
  used :: [Variable],             -- ^ A list of variables that have already been used.
  constraints :: ConstraintSet    -- ^ An atomic constraint set that cumulates the constraints of all the toplevel expressions.
}


-- | Definition of processing options specific to modules (as is not the case with the program options that affect
-- the whole program).
data MOptions = MOptions {
  toplevel :: Bool,               -- ^ Is the module at toplevel (in the sense : was it given as argument of the program).
  disp_decls :: Bool              -- ^ Display the variable declarations or not.
}



-- | Process a list of declarations (corresponding to either commands in interactive mode or
-- the body of a module). The arguments include os the vector of command options, the current module,
-- an extensive context, and a declaration.
process_declaration :: (Options, MOptions) -> S.Program -> ExtensiveContext -> S.Declaration -> QpState ExtensiveContext

-- EXPRESSIONS
process_declaration (opts, mopts) prog ctx (S.DExpr e) = do
  -- Translation of the expression into internal syntax.
  e' <- translate_expression e $ label ctx

  -- Free variables of the new expression
  fve <- return $ free_var e'
  a@(TBang n _) <- new_type
  specify_location n $ (case e' of
                          ELocated _ ex -> ex
                          _ -> extent_unknown)
  specify_expression n $ (ActualOfE e')

  -- ALL TOPLEVEL EXPRESSIONS MUST BE DUPLICABLE :
  set_flag n

  -- ALL VARIABLES ALREADY USED AND USED BY E MUST BE DUPLICABLE
  gamma <- return $ typing ctx
  (delta, _) <- sub_context (List.intersect fve $ used ctx) gamma
  fconstraints <- force_duplicable_context delta >>= Typing.TypeInference.filter

  -- Type e. The constraints from the context are added for the unification.
  (gamma_e, _) <- sub_context fve gamma
  cset <- constraint_typing gamma_e e' [a] >>= break_composite True
  cset' <- unify (not $ approximations opts) (cset <> fconstraints <> constraints ctx)
  inferred <- map_type a >>= pprint_type_noref

  -- Apply the substitution produced by the unification to the context gamma
  gamma <- IMap.foldWithKey (\x a rec -> do
                               m <- rec
                               a' <- map_type a
                               return $ IMap.insert x a' m) (return IMap.empty) gamma

  -- If interpretation, interpret, and display the result
  if runInterpret opts && toplevel mopts then do
    v <- interpret (environment ctx) e'
    case (v, circuitFormat opts) of
      (VCirc _ c _, "ir") -> do
          irdoc <- return $ export_to_IR c
          liftIO $ putStrLn irdoc
      (VCirc _ c _, "visual") ->
          liftIO $ putStrLn (pprint c ++ " : " ++ inferred)
      _ ->
          liftIO $ putStrLn (pprint v ++ " : " ++ inferred) 
  else if toplevel mopts then
    liftIO $ putStrLn ("-: "  ++ inferred)
  else
    return ()

  -- Return
  return $ ctx { used = List.union (used ctx) fve,     -- Used variables are augmented by the variables used in this expression.
                 constraints = cset' }                 -- The new constraints are those from the unification of the type of e.


-- LET BINDING
process_declaration (opts, mopts) prog ctx (S.DLet recflag p e) = do
  -- Translate pattern and expression into the internal syntax
  (p', lbl') <- translate_pattern p $ label ctx
  e' <- translate_expression e lbl'
  fve <- return $ free_var e'

  -- ALL VARIABLES ALREADY USED AND USED BY E MUST BE DUPLICABLE
  gamma <- return $ typing ctx
  (delta, _) <- sub_context (List.intersect fve $ used ctx) gamma
  fconstraints <- force_duplicable_context delta >>= Typing.TypeInference.filter

  csetup <- unify True (fconstraints <> constraints ctx)  -- Immediatly unify the new constraints

  -- Export the variables of the pattern
  p' <- export_pattern_variables prog p'

  -- Give the corresponding sub contexts
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
                 constraint_typing (gamma_p <+> gamma_e) e' [a]
             Nonrecursive -> do
                 -- If not recursive, do nothing
                 constraint_typing gamma_e e' [a]

  -- Unify the constraints produced by the typing of e (exact unification)
  cs <- break_composite True (csetp <> csete)  -- Break the composite constraints
  csete <- unify True cs                       -- Unify

  -- Last of the free variables of e - to be place after the unification, since
  -- the algorithm produces new variables that also have to be generic.
  endtype <- get_context >>= return . type_id
  endflag <- get_context >>= return . flag_id
  -- Apply the substitution produced by the unification of csett to the context gamma
  gamma <- IMap.foldWithKey (\x a rec -> do
                               m <- rec
                               a' <- map_type a
                               return $ IMap.insert x a' m) (return IMap.empty) gamma
  -- Generalize the types of the pattern (= polymorphism)
  gamma_p <- IMap.foldWithKey (\x a rec -> do
                                  ctx <- rec
                                  -- First apply the substitution
                                  a' <- map_type a
                                  
                                  -- Identify the free variables, the free variables form a subset of those used here.
                                  fv <- return $ List.union (free_typ_var a') (free_typ_var csete)
                                  ff <- return $ List.union (free_flag a') (free_flag csete)

                                  genfv <- return $ List.filter (\x -> limtype <= x && x < endtype) fv
                                  genff <- return $ List.filter (\f -> limflag <= f && f < endflag) ff

                                  gena <- return $ TForall genff genfv csete a'
                                  -- Update the global variables
                                  update_global_type x gena
                                  -- Update the typing context of u
                                  return $ IMap.insert x gena ctx) (return IMap.empty) gamma_p

  if disp_decls mopts then
    -- Print the types of the pattern p
    IMap.foldWithKey (\x a rec -> do
                        rec
                        nx <- variable_name x
                        pa <- pprint_type_noref a
                        -- No unnecessary printing
                        if toplevel mopts then
                          liftIO $ putStrLn (nx ++ " : " ++ pa)
                        else
                          return ()) (return ()) gamma_p
  else
    return ()

  -- Evaluation (even if the module is not toplevel, if the general optons want it to be evaluated, then so be it)
  if runInterpret opts then do
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
    return $ ctx { label = lbl',               -- Label updated with the bindings of p
                   typing = gamma_p <+> gamma, -- Typing context updated with the bindings of p
                   environment = env,          -- Environment updated with the bindings of p
                   constraints = csetup,       -- The constraints are added flag constraints
                   used = List.union (used ctx) fve }
  else
    return $ ctx { label = lbl',               -- Label updated with the bindings of p
                   typing = gamma_p <+> gamma, -- Typing context updated with the bindings of p
                   constraints = csetup,       -- The constraints are added flag constraints
                   used = List.union (used ctx) fve }




-- | Process a module, from the syntax translation to the type inference
-- Every result produced by the type inference is recorded in the module
-- internal representation (type Module)? The module options indicate whether
-- the toplevel expressions must be executed or not (amongst others). 
process_module :: (Options, MOptions) -> S.Program -> QpState ()
process_module opts prog = do

-- Configuration part
  -- Get the module name
  mod <- return $ S.module_name prog
  f <- return $ S.filepath prog

  -- Set up a new module
  ctx <- get_context
  set_context $ ctx { cmodule = Mod { module_name = mod,
                                      filepath = f,
                                      dependencies = S.imports prog,
                                      typespecs = Map.empty,
                                      global_ids = Map.empty,
                                      global_types = IMap.empty,
                                      global_vars = IMap.empty } }

  set_file f

  -- Import the global variables and types in the current context
  import_globals

  -- translate the module header : type declarations
  dcons <- import_typedefs (workWithProto $ fst opts) $ S.typedefs prog
  define_user_subtyping $ S.typedefs prog
  define_user_properties $ S.typedefs prog
  update_module_types

  cm <- get_module
  set_module $ cm { global_ids = dcons }

  -- Import the global variables from the dependencies
  gbls <- global_namespace
  -- Import the gloabl values from the dependencies
  env <- global_context

  -- Reset the circuit stack
  ctx <- get_context
  set_context $ ctx { circuits = [Circ { qIn = [], gates = [], qOut = [] }] }

--  t <- translate_body prog (S.body prog) (Map.union dcons gbls)
--  if proto then
--    unsugar t
--  else
--    return t

-- Type inference part

  -- Create the initial typing context
  gamma <- return IMap.empty
 
  -- Interpret all the declarations
  ctx <- List.foldl (\rec decl -> do
                       ctx <- rec
                       process_declaration opts prog ctx decl) (return $ Context { label = Map.union gbls dcons,
                                                                                   typing = IMap.empty,
                                                                                   environment = env,
                                                                                   used = [],
                                                                                   constraints = emptyset }) $ S.body prog

  -- All the variables that haven't been used must be duplicable
  (_, delta) <- sub_context (used ctx) (typing ctx)
  fconstraints <- force_duplicable_context delta >>= Typing.TypeInference.filter
  _ <- unify True (fconstraints <> constraints ctx)
 
  -- Return
  return ()


-- ==================================== --
-- | DO EVERYTHING !
-- To sort the dependencies of a list of modules, and e able to reuse the existing functions for single modules,
-- a dummy module is created that imports all the toplevel modules (never to be executed).
do_everything :: Options -> [FilePath] -> QpState ()
do_everything opts files = do
  -- Define the builtins
  import_builtins

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
                -- Move the module internally onto the modules stack
                ctx <- get_context
                set_context $ ctx { modules = (S.module_name p, cmodule ctx):(modules ctx) }
                return ()) (return ()) deps
-- ===================================== --


-- | A unification test : the unification alogorithm is run
-- on a set of typing constraints. It doesn't return anything, 
-- but prints the constraint after the unification
unification_test :: [(S.Type, S.Type)] -> IO String
unification_test set =
  let run = do
      set_verbose 2

      -- Translate the types in the internal syntax
      (constraints, _) <- List.foldl (\rec (t, u) -> do
                                        (r, lbl) <- rec
                                        (t', csett, lblt) <- translate_type t [] (lbl, False)
                                        (u', csetu, lblu) <- translate_type u [] (lblt, False)
                                        return ([t' <: u'] <> csett <> csetu <> r, lblu)) (return (emptyset, Map.empty)) set
      newlog 1 $ pprint constraints

      -- Run the unification algorithm
      constraints <- break_composite True constraints
      newlog 1 $ pprint constraints

      -- Unification
      constraints <- unify True constraints
      return $ pprint constraints
  in
  do
    (_, s) <- runS run empty_context
    return s


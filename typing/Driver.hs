module Driver where

import Classes
import Utils
import QuipperError

import Lexer
import Parser
import Localizing (clear_location)

import qualified Syntax as S
import Printer
import CoreSyntax
import TransSyntax

import Gates

import Ordering
import TypeInference

import QpState
import TypingContext
import Modules

import System.Directory

import Data.List as List
import Data.Map as Map
import Data.IntMap as IMap
import Data.Char as Char

-- Import the gates into the current context
gate_context :: [(String, S.Type)] -> QpState TypingContext
gate_context gates = do
  List.foldl (\rec (s, t) -> do
                ctx <- rec
                (t', _) <- translate_type t [] (Map.empty)
                x <- gate_id s
                bind_var x t' ctx) (return IMap.empty) gates

-- | Lex and parse a file located by the given filepath
lex_and_parse_implementation :: FilePath -> QpState S.Program
lex_and_parse_implementation file = do
  contents <- liftIO $ readFile file
  tokens <- liftIO $ mylex file contents
  mod <- return $ module_of_file file
  return $ (parse tokens) { S.mname = mod, S.filepath = file }


-- | Find the implementation of a module in a given directory
-- The name of the code file is expected to be dir/module.ext,
-- where dir is the directory, module is the name of the module with
-- the first letter put to lower case, and ext the extension, which can be either .qp (implementation)
-- or .qpi (interface). 'dir' is taken in the provided list of directories
--
-- If several implementations are found, an error is raised
find_in_directories :: String -> [FilePath] -> String -> QpState (Maybe FilePath)
find_in_directories mod@(initial:rest) directories extension = do
  mfile <- return $ (Char.toLower initial):(rest ++ extension)
  existing <- List.foldl (\rec d -> do
                            r <- rec
                            nexttry <- return $ d ++ mfile
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
-- file is found
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
-- Since the interface file is optional, so is the return value
find_interface_in_directories :: String -> [FilePath] -> QpState (Maybe FilePath)
find_interface_in_directories mod directories =
  find_in_directories mod directories ".qpi"


-- | Recursively explore the dependencies of the program. It returns
-- a map linking the modules to their parsed implementation, and a map corresponding
-- to the dependency graph
-- It proceeds to sort topologically the dependencies at the same time, using an in-depth exploration of the graph
-- Note that the return list is reversed, with the 'oldest' module first
explore_dependencies :: [String] -> S.Program -> Map String S.Program -> [S.Program] -> QpState [S.Program]
explore_dependencies dirs prog mods sorted = do
  -- Mark the module as explored
  mods <- return $ Map.insert (S.mname prog) prog mods
  -- Sort the dependencies
  sorted <- List.foldl (\rec m -> do
                           sorted <- rec
                           case (Map.lookup m mods, List.find (\p -> S.mname p == m) sorted) of
                             -- Nothing to do
                             (Just _, Just _) ->
                                 return sorted

                             (Just _, Nothing) ->
                                 -- The module has already been visited : cyclic dependency
                                 throwQ $ CyclicDependencies (S.mname prog)

                             -- Explore
                             _ -> do
                                 file <- find_implementation_in_directories m dirs
                                 p <- lex_and_parse_implementation file
                                 explore_dependencies dirs p mods sorted) (return sorted) (S.imports prog)
  -- Push the module on top of the list : after its dependencies
  return (prog:sorted)


-- | Sort the dependencies of file in a topological fashion
-- The program argument is the main program, on which quipper has been called. The return value
-- is a list of the dependencies, with the properties :
--      - each module may only appear once
--      - for each module, every dependent module is placed before in the list
--      - (as a corollary) the main module is placed last
build_dependencies :: [String] -> S.Program -> QpState [S.Program]
build_dependencies dirs main = do
  deps <- explore_dependencies dirs main (Map.empty) []
  return $ List.reverse deps


-- | Process a module, from the syntax translation to the type inference
-- Every result produced by the type inference is recorded in the module
-- internal representation (type Module)
process_module :: Bool -> S.Program -> QpState Type
process_module exact prog = do

-- Configuration part
  -- Get the module name
  mod <- return $ S.mname prog
  f <- return $ S.filepath prog

  -- Convert and import the type definitions
  dcons <- import_typedefs $ S.typedefs prog
  define_user_subtyping $ S.typedefs prog

  -- Set up a new module
  ctx <- get_context
  set_context $ ctx { cmodule = Mod { mname = mod,
                                      codefile = f,
                                      dependencies = S.imports prog,
                                      global_ids = dcons,
                                      global_types = IMap.empty } }

  set_file f
  import_globals

-- Translation part

  -- Import the global variables from the dependencies
  gbls <- global_namespace

  -- Translate the body of the module
  cprog <- translate_body (S.body prog) (Map.union dcons gbls)

-- Type inference part

  -- Create the initial typing context
  typctx <- return $ IMap.empty
  
  -- Create the initial type
  a <- new_type

  -- | constraint typing | --
  constraints <- constraint_typing typctx cprog a
  newlog 1 ">> Initial constraint set"
  newlog 1 $ pprint constraints ++ "\n"

  -- | Unification | --
  constraints <- break_composite True constraints
    -- For ordering purposes
  register_constraints $ fst constraints
  constraints <- unify exact constraints
  newlog 1 ">> Unified constraint set"
  newlog 1 $ pprint constraints ++ "\n"

  -- Application of the solution map to the initial type
  inferred <- map_type a
  newlog 1 $ ">> Inferred type : " ++ pprint inferred

  -- Solve the remaining flag constraints,
  -- and apply the result to the inferred type to get the final answer
  solve_annotation $ snd constraints
  inferred <- rewrite_flags inferred
  newlog 1 $ ">> Inferred type, references removed : " ++  pprint inferred ++ "\n"

  -- Same with the export variables
  ctx <- get_context
  exp <- return $ IMap.assocs $ global_types (cmodule ctx)
  exp <- List.foldl (\rec (x, a) -> do
                       r <- rec
                       a' <- map_type a
                       return ((x, a'):r)) (return []) exp
  set_context $ ctx { cmodule = (cmodule ctx) { global_types = IMap.fromList exp } }

  newlog 0 ">> Export variables"
  List.foldl (\rec (x, a) -> do
                rec
                n <- variable_name x
                newlog 0 $ n ++ " :: " ++ pprint a) (return ()) exp
  newlog 0 "<<\n"
  
  -- Return the inferred type 
  return inferred


-- ==================================== --
-- | DO EVERYTHING !
do_everything :: [String] -> Bool -> FilePath -> QpState Type
do_everything dirs exact file = do
  -- Parse the original file
  prog <- lex_and_parse_implementation file

  -- Build the dependencies
  deps <- build_dependencies dirs prog

  -- Process everything, finishing by the main file
  List.foldl (\rec p -> do
                _ <- rec
                typ <- process_module exact p
                -- Move the module internally onto the modules stack
                ctx <- get_context
                set_context $ ctx { modules = (S.mname p, cmodule ctx):(modules ctx) }
                -- Return the last type
                return typ) (return (TBang (-1) TUnit)) deps
-- ===================================== --


-- | A unification test : the unification alogorithm is run
-- on a set of typing constraints. It doesn't return anything, 
-- but prints the constraint after the unification
unification_test :: [(S.Type, S.Type)] -> IO String
unification_test set =
  let run = do
      -- Translate the types in the internal syntax
      constraints <- List.foldl (\rec (t, u) -> do
                                   r <- rec
                                   (t', csett) <- translate_type t [] (Map.empty)
                                   (u', csetu) <- translate_type u [] (Map.empty)
                                   return $ [t' <: u'] <> csett <> csetu <> r) (return emptyset) set

      -- Run the unification algorithm
      constraints <- break_composite True constraints

      -- Unification
      register_constraints $ fst constraints
      constraints <- unify True constraints

      return $ pprint constraints
  in
  do
    (_, s) <- runS run QpState.empty_context
    return s


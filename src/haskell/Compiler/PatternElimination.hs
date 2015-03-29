-- | This module implements a method used to simplify the original expression. In particular, the
-- implementation of the data constructors is made explicit, and the patterns are destructed, through
-- the means of:
--
-- * the /n/th element of a tuple is accessed through the functions Access_1, Access_2, ..
--
-- * the label or tag of a record or data constructor is accessed using Label.
--
-- * the information contained in a record in accessed via Body_datacon.
--
-- The tests of the case expressions are make explicit. Using a decision tree and chosen heuristics,
-- a tree close to the optimal is produced. This tree can then be used to generate the series of
-- instructions needed to discriminate the patterns.
--
-- The patterns are also removed from the let expressions and the function arguments. Note that the
-- type constraints and location information are also removed.

module Compiler.PatternElimination where

import Classes
import Utils
import Parsing.Location

import Language.Constructor

import Monad.Core hiding (warning)
import Monad.Typer (solveType, typeOf)
import Monad.Compiler
import Monad.Error

import qualified Core.Syntax as C

import Compiler.Overloading
import Compiler.SimplSyntax
import Compiler.Circuits

import Data.List as List
import Data.Map as Map
import Data.IntMap as IntMap


-- | Representation of a decision tree, which describes the tests needed to solve a pattern matching.
-- Each node represents a test to perform, and the actions to take depending on the result of the
-- test (which can be to perform another test).
data DecisionTree =
  -- | The compiler will, in this case, generate the code responsible for extracting the test parameter,
  -- and build a switch case with all targets recursively constructed.
    Test TestLocation [(TestResult, DecisionTree)]
  -- | Identified match success (represents the index of the case, a failed pattern matching is
  -- represented by a negative value).
  | Result Int
  deriving Show

-- | Ways of locating it self in a pattern. The constructors indicate the action to take next.
data NextStep =
    InTuple Int        -- ^ The information is the Nth element of a tuple.
  | InDatacon Datacon  -- ^ The information is the argument of a record.
  | InTag Algebraic    -- ^ The information is the label of a record (=true pattern matching).
  deriving (Show, Eq, Ord)

-- | Position of the information relevant to a test in a pattern.
type TestLocation = [NextStep]

-- | The result of a test.
data TestResult =
    RInt Int                -- ^ The result of the test is an integer.
  | ROtherInt [Int]         -- ^ Represents the set of all the integers not listed by the argument.
  | RBool Bool              -- ^ The result is a boolean.
  | RDatacon Datacon        -- ^ The result is a data constructor.
  | ROtherDatacon [Datacon] -- ^ The result is a constructor not listed by the argument.
  deriving (Show, Eq)


-- | Return the kind of a list of results. It is typically a result of the list, as type checking
-- ensures no heterogenous pattern matching will occur.
resultKind :: [TestResult] -> TestResult
resultKind [] = throwNE $ ProgramError "PatternElimination:resultKind: empty list"
resultKind (RInt _:_) = RInt 0
resultKind (ROtherInt _:_) = RInt 0
resultKind (RBool _:_) = RBool True
resultKind (RDatacon _:_) = RDatacon 0
resultKind (ROtherDatacon _:_) = RDatacon 0

-- | On the supposion that the result is 'RInt', return the associated integer.
intResult :: TestResult -> Int
intResult (RInt i) = i
intResult _ = 0

-- | On the supposition that the result is 'RDatacon', return the associated constructor.
consResult :: TestResult -> Datacon
consResult (RDatacon d) = d
consResult _ = 0


-- | Build the list of the tests relevant to a pattern matching case, meaning all the tests that must
-- be checked true for the pattern matching case to be accepted.
-- TODO: tail rec implementation.
relevantTests :: C.Pattern -> Compiler [(TestLocation, TestResult)]
relevantTests pattern = relevantTestsAux [] pattern
  where
    -- The additional argument is the reversed location in the pattern.
    relevantTestsAux :: TestLocation -> C.Pattern -> Compiler [(TestLocation, TestResult)]
    relevantTestsAux location (C.PConstant _ (ConstInt n)) = return [(List.reverse location, RInt n)]
    relevantTestsAux location (C.PConstant _ (ConstBool b)) = return [(List.reverse location, RBool b)]
    relevantTestsAux location (C.PConstant _ ConstUnit) = return []
    relevantTestsAux location (C.PWildcard _) = return []
    relevantTestsAux location (C.PVar _ _) = return []
    relevantTestsAux location (C.PDatacon _ cons arg) = do
      typ <- runCore $ getConstructorSourceType cons
      all <- runCore $ getAllConstructors typ
      -- Sub-pattern tests.
      tests <-
        case arg of
          Just pattern -> relevantTestsAux ((InDatacon cons):location) pattern
          Nothing -> return []
      -- Only one constructor: trivial pattern matching.
      -- Else add a test to check the constructor.
      if List.length all == 1 then return tests
      else do
        let test = (List.reverse $ (InTag typ):location, RDatacon cons)
        return $ test:tests
    relevantTestsAux location (C.PCoerce pattern _ _) = relevantTestsAux location pattern
    relevantTestsAux location (C.PTuple _ tuple) = do
      (_, tests) <- List.foldl (\rec pattern -> do
          (i, tests) <- rec
          more <- relevantTestsAux ((InTuple i):location) pattern
          return (i+1, more ++ tests)
        ) (return (0, [])) tuple
      return tests


-- | Build a pattern matching a test.
patternOfTest :: C.Pattern -> TestLocation -> TestResult -> C.Pattern
patternOfTest p [] (ROtherInt ns) = C.PVar (C.patternInfo p) 0 -- Will be replaced.
patternOfTest p _ (ROtherDatacon ns) = C.PVar (C.patternInfo p) 0 -- Will be replaced.
patternOfTest p [] (RInt n) = C.PConstant (C.patternInfo p) $ ConstInt n
patternOfTest p [] (RBool b) = C.PConstant (C.patternInfo p) $ ConstBool b
patternOfTest (C.PTuple r tuple) ((InTuple n):ns) res =
  let tuple' = List.map (\(m, p) ->
        if n == m then patternOfTest p ns res
        else p
        ) $ List.zip [0..List.length tuple-1] tuple in
  C.PTuple r tuple'
patternOfTest (C.PDatacon info cons (Just _)) [InTag _] (RDatacon cons') =
  C.PDatacon info cons' $ Just $ C.PWildcard info
patternOfTest (C.PDatacon info cons Nothing) [InTag _] (RDatacon cons') =
  C.PDatacon info cons' Nothing
patternOfTest (C.PDatacon info cons (Just p)) ((InDatacon _):ns) res =
  let p' = patternOfTest p ns res in
  C.PDatacon info cons $ Just p'
patternOfTest (C.PVar info _) _ _ = C.PWildcard info
patternOfTest _ _ _ = throwNE $ ProgramError "PatternElimination:patternOfTest: illegal arguments"


-- | Complete a partial decision tree. The input corresponds to a branch in the decision tree. The
-- different inputs can be interpreted as follow; if the list of patterns is empty, the matching is
-- non-exhaustive (a series of tests lead to a non existent test case) ; if the list of remaining tests
-- is empty, and only one pattern remains, we have safely identified the test case ; if the list is
-- empty but more that one pattern remains, we have redundant cases: keep the first one in the list.
-- In all other cases, we must build more tests to decide the case.
buildPartialTree :: [C.Pattern]
                -> [(TestLocation, [(Int, TestResult)])]
                -> [Int] -> Compiler (DecisionTree, [String])
-- Non-exhaustive pattern matching: a series of tests lead to a non existant test case. The program
-- will be redirected to an matching error.
buildPartialTree _ _ [] = return (Result $ -1, [])
-- Successful case matching.
buildPartialTree _ [] [n] = return (Result n, [])
-- Redundant case matching; keep only the first case in the list of test cases.
buildPartialTree _ [] (n:ns) = return (Result n, [])
-- Undecided pattern matching; choose a test to perform and recursively call the builder. The next
-- test is based on the following heuristic:
--
--    * always pick up the nearest test (e.g. we can't test the third element of a list before being
--      sure the list is actually that long).
--    * choose in preference the tests relevant to the first test cases.
--    * if the first two conditions did not return anythig, compare the branching factor: the number
--      of expected results for a test.
--
buildPartialTree realPatterns tests @ (t:ts) patterns = do
  -- Choose the following test.
  let next = List.foldl (\(location, results) (location', results') ->
        -- Test the validity of the comparison (always choose the shortest path).
        if List.length location' < List.length location then (location', results')
        else if List.length location < List.length location' then (location, results)
        -- Compare the lowest relevant pattern.
        else
          let min = List.minimum $ List.map fst results
              min' = List.minimum $ List.map fst results' in
          if min' < min then (location', results')
          else if min < min' then (location, results)
          -- If the previous test didn't work, compare the branching factor.
          else
            let branching = List.length $ List.nub $ List.map snd results
                branching' = List.length $ List.nub $ List.map snd results' in
            if branching' < branching then (location', results')
            else (location, results)
        ) t ts

  -- Once the test has been decided, gather the possible results.
  let results = List.nub $ List.map snd $ snd next
  -- Complete the list of results by adding missing cases: the set of remaining integers for int
  -- tests; true or false for boolean tests; the missing data constructors for pattern tests.
  results <- case List.head results of
      -- If the result is an integer, all the possible results are the ones listed here, plus the
      -- remaining integers in ROtherInt.
      RInt _ -> return $ (ROtherInt $ List.map intResult results):results
      -- If the result is a boolean, the possible results are always true or false.
      RBool _ -> return [RBool True, RBool False]
      -- If the result is a data constructor, all the possible results are the constructors from the
      -- same type.
      RDatacon cons -> do
        typ <- runCore $ getConstructorSourceType cons
        all <- runCore $ getAllConstructors typ
        -- If not all datacons are listed, add another result of the form ROtherDatacon.
        if List.length results < List.length all then
          return $ (ROtherDatacon $ List.map consResult results):results
        else return results
      -- Other cases are not relevant here.
      _ -> return results

  -- Remove the selected test from the list.
  let tests' = List.delete next tests
  -- Call 'buildPartialTree' on each possible result to complete the subtree. The list of unmatched
  -- cases is returned as a by-product.
  (subtrees, unmatched) <- List.foldl (\rec result -> do
      (subtrees, unmatched) <- rec
      -- List of the patterns matching this condition.
      let matchingCases = List.filter (\pattern ->
            case List.lookup pattern (snd next) of
              Just result' -> result' == result
              -- This case corresponds to the patterns var and wildcard,
              -- that match everything and yet are not relevant
              Nothing -> True
            ) patterns
      -- List of the tests relevant for these patterns. Also, remove the uneeded results in each of
      -- the tests.
      let relevantTests =
            List.filter (\(_, results) ->
                List.intersect (List.map fst results) matchingCases /= []) tests'
          relevantTests' =
            List.map (\(test, results) ->
                (test, List.filter (\(pattern, _) -> List.elem pattern matchingCases) results)
              ) relevantTests
      -- If no test is relevant to the FIRST pattern, then it passes all the tests.
      case matchingCases of
        -- A matching error. Build a clear error message describing a passing specimen and pass it to
        -- the list of unmatched cases.
        [] -> do
          -- Modify the pattern to display the structure of the test (unfold the test location).
          let pcase = patternOfTest (realPatterns !! List.head patterns) (fst next) result
          -- Printing the pattern.
          pCons <- runCore displayConstructor
          let printout = genprint Inf [\_ -> "x", pCons] pcase
          -- In case the expected result is 'ROtherInt' or 'ROtherDatacon', display the list of
          -- non-admissible integers as well.
          let printout' =
                case result of
                  ROtherInt [i] -> printout ++ " where x /= " ++ show i
                  ROtherDatacon [d] -> printout ++ " where x /= " ++ pCons d
                  ROtherInt (i:is) ->
                    printout ++ " where x /= {" ++
                    show i ++ List.foldl (\s i -> s ++ ", " ++ show i) "" is ++ "}"
                  ROtherDatacon (d:ds) ->
                    printout ++ " where x /= {" ++
                    pCons d ++ List.foldl (\s d -> s ++ ", " ++ pCons d) "" ds ++ "}"
                  _ -> printout
          return ((result, Result $ -1):subtrees, printout':unmatched)

        n:_ -> do
          -- Count the tests relevant to this particular pattern.
          let rtests = List.filter (\(_, results) -> List.elem n $ List.map fst results) relevantTests'
          if List.length rtests == 0 then
            -- No need to take other tests.
            return ((result, Result n):subtrees, unmatched)
          else do
            -- Else, do the normal stuff. Build the subtree and return the rest.
            (subtree, unmatched') <- buildPartialTree realPatterns relevantTests' matchingCases
            return ((result, subtree):subtrees, unmatched'++unmatched)
    ) (return ([], [])) results

  -- Assemble the final tree.
  return (Test (fst $ next) subtrees, unmatched)



-- | Build an optimized decision tree for a pattern matching. The function tries to optimize the
-- matching by placing the most indicative tests first (while keeping the semantics of the original
-- pattern matching).
buildDecisionTree :: [C.Pattern] -> Compiler DecisionTree
buildDecisionTree patterns = do
  -- Build the relevant tests first. Patterns are numbered from left to right, from 0 to n-1. For
  -- each test, the list of patterns for which it is relevant is added, along with the list of possible
  -- values.
  (_, tests) <- List.foldl (\rec pattern -> do
      (n, tests) <- rec -- n is the index of the case in the pattern matching.
      relevant <- relevantTests pattern
      let tests' =
            List.foldl (\tests (test, result) ->
                case Map.lookup test tests of
                  Nothing -> Map.insert test [(n, result)] tests
                  Just results -> Map.insert test ((n, result):results) tests
              ) tests relevant
      return (n+1, tests')
    ) (return (0, Map.empty)) patterns
  -- Build the decision tree.
  (tree, unmatched) <- buildPartialTree patterns (Map.assocs tests) [0..(List.length patterns)-1]
  -- If non exhaustive match, send a warning.
  let unmatched' = List.nub unmatched
  if unmatched' == [] then return ()
  else warning (UnexhaustiveMatch unmatched') Nothing
  -- Return the decision tree.
  return tree


-- | Extract the variables of a pattern, and return the sequence of functions applications necessary
-- to retrieve them.
patternVariables :: C.Pattern -> [(TestLocation, Variable)]
patternVariables pattern =
  readVars [] pattern
  where
    readVars :: TestLocation -> C.Pattern -> [(TestLocation, Variable)]
    readVars loc (C.PVar _ x) = [(List.reverse loc, x)]
    readVars loc (C.PDatacon _ cons (Just arg)) = readVars ((InDatacon cons):loc) arg
    readVars loc (C.PCoerce pattern _ _) = readVars loc pattern
    readVars loc (C.PTuple _ tuple) =
      snd $ List.foldl (\(n, vars) pattern ->
          let vars' = readVars ((InTuple n):loc) pattern in
          (n+1, vars' ++ vars)
        ) (0, []) tuple
    readVars _ _ = []


-- | Find the extracted variable closest to the information one wants to extract.
longestPrefix :: [(TestLocation, Variable)] -> TestLocation -> (TestLocation, Variable, TestLocation)
longestPrefix extracted test =
  List.foldl (\(loc, var, suffix) (loc', var') ->
      case List.stripPrefix loc' test of
        -- Incompatible paths.
        Nothing -> (loc, var, suffix)
        -- Common prefix, keep the longest.
        Just suffix' ->
          if List.length suffix' <= List.length suffix then (loc', var', suffix')
          else (loc, var, suffix)
    ) ([], -1, test) extracted


-- | Complete the extraction of a piece of information. The argument should be the variable closest
-- to the information we want to access. The function then applies the operations necessary to go
-- from this variable, to the information required. Each variable extracted in the process is added
-- to the list of extractions.
extractTest :: (TestLocation, Variable, TestLocation) -> Compiler (Expr -> Expr, [(TestLocation, Variable)], Variable)
extractTest (prefix, x, loc) =
  case loc of
    -- No further steps required to obtain the variable: return the identity.
    [] -> return ((\e -> e), [], x)
    -- Perform the next step of the extraction, while storing the result in a temporary variable. The
    -- function 'extracTest' is called again to finish the extraction.
    l:ls -> do
      x' <- createVariable "x"
      exp <- case l of
          InTuple n -> return $ EAccess n x
          InDatacon cons -> do
              cinfo <- runCore $ getConstructorInfo cons
              return $ extract cinfo x
          InTag typ -> runCore $ getTag typ x

      let nprefix = prefix ++ [l]
      (cont, extracted, endvar) <- extractTest (nprefix, x', ls)
      return (\e -> ELet x' exp $ cont e, (nprefix, x'):extracted, endvar)


-- | Same as extract, except that the variable holding the information is specified beforehand.
extractVar :: (TestLocation, Variable, TestLocation) -> Variable -> Compiler (Expr -> Expr, [(TestLocation, Variable)])
extractVar (prefix, x, loc) endvar =
  case loc of
    -- The variable 'x' already contains what we want.
    [] -> return ((\e -> ELet endvar (EVar x) e), [])
    -- The LAST action is a tuple accessor.
    [InTuple n] -> return (\e -> ELet endvar (EAccess n x) e, [])
    -- The LAST action is a destructor.
    [InDatacon cons] -> do
      cinfo <- runCore $ getConstructorInfo cons
      return (\e -> ELet endvar (extract cinfo x) e, [])

    -- Else use an intermediary variable.
    l:ls -> do
      x' <- createVariable "x"
      exp <- case l of
          InTuple n -> return $ EAccess n x
          InDatacon cons -> do
            cinfo <- runCore $ getConstructorInfo cons
            return $ extract cinfo x
          InTag typ -> runCore $ getTag typ x

      let nprefix = prefix ++ [l]
      (cont, extracted) <- extractVar (nprefix, x', ls) endvar
      return (\e -> ELet x' exp $ cont e, (nprefix, x'):extracted)


-- | Transform the decision tree produced by the methods above into an expression again. The first
-- argument is the initial list of test cases, the second is the decision tree to transform, the third
-- the list of extracted pattern location.
flattenDecisionTree :: [C.Binding] -> DecisionTree -> [(TestLocation, Variable)] -> Compiler Expr
-- The subtree ends in an unmatched case ; geneate a code returning an matching error.
flattenDecisionTree _ (Result (-1)) _ = return $ EError "Pattern Error"
-- Success case.
flattenDecisionTree cases (Result n) extracted = do
  -- Get the corresponding test cases from the list.
  let C.Binding binder e = cases List.!! n
  let vars = patternVariables binder
  -- Remove the patterns from the expression en.
  e' <- removePatterns e
  -- Extract the variables bound in the pattern.
  (initseq, _) <- List.foldl (\rec (loc, x) -> do
      (cont, extracted) <- rec
      let (prefix, x', loc') = longestPrefix extracted loc
      (cont', updates) <- extractVar (prefix, x', loc') x
      return (cont . cont', updates ++ extracted)
    ) (return (id, extracted)) vars
  -- Allocate the variables, and build the final expression.
  return $ initseq e'
-- Test case.
flattenDecisionTree cases (Test test results) extracted = do
  -- Extract the object of the test.
  let (prefix, x, loc) = longestPrefix extracted test
  (initseq, updates, x') <- extractTest (prefix, x, loc)
  let extracted' = updates ++ extracted
  -- Build the switch condition.
  switch <- case resultKind $ List.map fst results of
    RInt _ -> do
      -- Isolate the infinite case (always present), and build the corresponding subtree calling the
      -- function recursively.
      let (def, others) = List.partition (\(r, _) ->
            case r of ROtherInt _ -> True; _ -> False) results
      remains <- case def of
            [(_, rem)] -> return rem
            _ -> fail "PatternElimination:simplifyPatternMatching: missing case OtherInt"
      lastcase <- flattenDecisionTree cases remains extracted'
      -- Eliminate the cases with the same results as the infinite case (= Result -1).
      let others' = List.filter (\(res, subtree) ->
            case subtree of Result (-1) -> False; _ -> True) others
      -- Build the subtress for all the remainging possibilities.
      cases <- List.foldl (\rec (rint, subtree) -> do
            let n = intResult rint
            tests <- rec
            testn <- flattenDecisionTree cases subtree extracted'
            return $ (n, testn):tests
          ) (return []) others
      -- Build the completed expression.
      return $ EMatch (EVar x') cases lastcase

    RBool _ -> do
      -- Isolate each posibility. The default case of the switch will always be the false case.
      rtrue <- case List.lookup (RBool True) results of
            Just t -> return t
            Nothing -> fail "PatternElimination:simplifyPatternMatching: missing case True"
      rfalse <- case List.lookup (RBool False) results of
            Just t -> return t
            Nothing -> fail "PatternElimination:simplifyPatternMatching: missing case False"
      casetrue <- flattenDecisionTree cases rtrue extracted'
      casefalse <- flattenDecisionTree cases rfalse extracted'
      return $ EMatch (EVar x') [(1, casetrue)] casefalse

    RDatacon _ -> do
        -- Lookup the ROtherDataon case.
        let (remain, others) = List.foldl (\(remain, others) (r, subtree) ->
                case r of
                  ROtherDatacon _ -> (Just (r, subtree), others)
                  _ -> (remain, (r,subtree):others)
              ) (Nothing, []) results
        -- Build the standard cases.
        branches <- List.foldl (\rec (rcons, subtree) -> do
            branches <- rec
            tag <- case rcons of
                RDatacon cons -> do
                  info <- runCore $ getConstructorInfo cons
                  return $ tag info
                _ -> return (-1)
            e <- flattenDecisionTree cases subtree extracted'
            return $ (tag, e):branches) (return []) others
        -- Build the default case: ROtherDatacon if present, else one of the test results.
        case remain of
          Nothing -> return $ EMatch (EVar x') (List.init branches) $ snd $ List.last branches
          Just (_, subtree) -> do
              e <- flattenDecisionTree cases subtree extracted'
              return $ EMatch (EVar x') branches e

    ROtherInt _ -> fail "PatternElimination:simplifyPatternMatching: unexpected result 'ROtherInt'"
    ROtherDatacon _ -> fail "PatternElimination:simplifyPatternMatching: unexpected result 'ROtherDatacon'"

  -- Complete the sequence with the variable extraction.
  return $ initseq switch


-- | Remove the patterns. Some are left in the match expressions, but should only be of the form
-- @A _@ or @_@, where @_@ is the wildcard.
removePatterns :: C.Expr -> Compiler Expr
removePatterns (C.EVar _ x) = return $ EVar x
removePatterns (C.EGlobal _ x) = return $ EGlobal x
removePatterns (C.ECoerce e _) = removePatterns e
removePatterns (C.EError msg) = return $ EError msg
removePatterns (C.EConstant _ c) = return $ EConstant c

removePatterns (C.EApp e f) = do
  e' <- removePatterns e
  f' <- removePatterns f
  return $ EApp e' f'

removePatterns (C.ETuple _ tuple) = do
  tuple' <- List.foldl (\rec e -> do
      tuple <- rec
      e' <- removePatterns e
      return $ e':tuple) (return []) tuple
  return $ ETuple $ List.reverse tuple'

removePatterns (C.EIf e f g) = do
  e' <- removePatterns e
  f' <- removePatterns f
  g' <- removePatterns g
  return $ EMatch e' [(1, f')] g'

removePatterns (C.EBox _ typ) = do
  let typ' = C.quantumTypeOfType typ
  x <- request_box typ'
  return $ EVar x

removePatterns (C.EUnbox info) = do
  typ <- runTyper $ solveType $ C.typ info
  let (t, u) = C.circuitTypeOfType typ
  -- Check the type of the unbox operator.
  if not $ C.isConcrete typ then do
    warning AmbiguousUnbox $ Just $ C.extent info
    return $ int 0
  else do
    x <- request_unbox (t,u)
    return $ EVar x

removePatterns (C.ERev _) = do
  x <- request_rev
  return $ EVar x

-- If the data constructor expected an argument, then return a pointer to an implementation of the
-- incomplete constructor. Else build the data constructor as intructed in its definition.
removePatterns (C.EDatacon _ cons Nothing) = do
  info <- runCore $ getConstructorInfo cons
  if implementation info == -1 then do
    builder <- case build info of
        Left builder -> return builder
        _ -> fail "PatternElimination:removePatterns: wrong data constructor application"
    return builder
  else return $ EGlobal $ implementation info

-- The data constructor already has tis argument; we can build the constructor immediatly as instructed
-- in the definition.
removePatterns (C.EDatacon _ cons (Just e)) = do
  info <- runCore $ getConstructorInfo cons
  builder <- case build info of
      Right builder -> return builder
      _ -> fail "PatternElimination:removePatterns: wrong data constructor application"
  e' <- removePatterns e
  return $ builder e'

-- For pattern matching, call the dedicated function.
removePatterns (C.EMatch _ test cases) = do
  let patterns = List.map C.binder cases
  test' <- removePatterns test
  tree <- buildDecisionTree patterns
  -- If the test expression is not a variable, then push it in a variable.
  case test' of
    EVar init -> flattenDecisionTree cases tree [([], init)]
    _ -> do
        init <- createVariable "x"
        tests <- flattenDecisionTree cases tree [([], init)]
        return $ ELet init test' tests

-- Intercept recursive functions.
removePatterns (C.ELet Recursive (C.PVar _ v) e f) = do
  e' <- removePatterns e
  f' <- removePatterns f
  case e' of
    EFun x e -> return $ ELet v (EFix v x e) f'
    _ -> fail "PatternElimination:removePatterns: unauthorized recursive data"

-- Let bindings with a variable as pattern can be directly translated into the simplified syntax
-- without having to build a pattern matching.
removePatterns (C.ELet _ (C.PVar _ v) e f) = do
  e' <- removePatterns e
  f' <- removePatterns f
  return $ ELet v e' f'

-- The wildcard pattern is converted into an instruction sequence, structure that has been introduced
-- in the simplified syntax.
removePatterns (C.ELet _ (C.PWildcard _) e f) = do
  e' <- removePatterns e
  f' <- removePatterns f
  return $ ESeq e' f'

-- If the pattern is more complex (e.g. includes numeric values), we have it go through the
-- simplification of pattern matching, which manages matching errors and extracts the pattern variables
-- at the same time.
removePatterns (C.ELet Nonrecursive p e f) = do
  let info = C.Info unknownExtent C.int
  removePatterns $ C.EMatch info e [C.Binding p f]

-- Unsupported mutually recursive structures / functions.
removePatterns (C.ELet Recursive _ _ _) =
  fail "PatternElimination:removePatterns: unexpected recursive binding"

-- For functions, the extraction of the variables of the function argument is done through the
-- generation of a let binding.
removePatterns (C.EFun info arg body) = do
  case arg of
    -- The pattern is already a variable, the function can be transformed directly.
    C.PVar _ x -> do
      body' <- removePatterns body
      return $ EFun x body'
    -- The pattern is the wildcard: do nothing (except from creating a variable for the argument).
    C.PWildcard _ -> do
      body' <- removePatterns body
      x <- createVariable "x"
      return $ EFun x body'
    -- If the pattern is more complex, replace it by a variable and use a let binding to extract the
    -- bound variables.
    _ -> do
      x <- createVariable "x"
      body' <- removePatterns $ C.ELet Nonrecursive arg (C.EVar info x) body
      return $ EFun x body'


-- | Remove the patterns from all the toplevel declarations.
transformDeclarations :: [C.Declaration] -> Compiler [Declaration]
transformDeclarations decls = do
  decls <- List.foldl (\rec declaration -> do
      decls <- rec
      case declaration of
        C.DExpr info e -> do
          warning NakedExpressionToplevel $ Just $ C.extent info
          return decls

        C.DLet _ recflag x e -> do
          e' <- removePatterns e
          case (recflag, e') of
            (Recursive, EFun arg e) -> return $ (DLet External x $ EFix x arg e):decls
            (Nonrecursive, EFun arg e) -> return $ (DLet External x $ EFun arg e):decls
            _ -> do
              scheme <- runTyper $ typeOf x
              let typ = C.typeOfScheme scheme
              if isFunction typ then do
                -- Necessary eta-expansion.
                a <- createVariable "x"
                return $ (DLet External x $ EFun a $ EApp e' $ EVar a):decls
              else return $ (DLet External x e'):decls

    ) (return []) decls

  -- Retrieve the declaration of quantum operations and add them at the beginning of the module.
  circuits <- clearCircuitLibrary
  return $ circuits ++ List.reverse decls

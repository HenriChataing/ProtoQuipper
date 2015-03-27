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

--import Parsing.Location

import Language.Constructor

import Monad.Core (getConstructorSourceType)
import Monad.Compiler
import Monad.Error

import qualified Core.Syntax as C

import Compiler.Overloading
import Compiler.SimplSyntax
import Compiler.Circuits

import Data.List as List
import Data.Map as Map
import Data.IntMap as IntMap


-- | Return True iff the type contains no variables.
--is_concrete :: QuantumType -> Bool
--is_concrete QQubit = True
--is_concrete QUnit = True
--is_concrete (QVar _) = False
--is_concrete (QTensor qlist) =
--  List.and $ List.map is_concrete qlist


-- | Convert back a circuit type to the type of an unbox operator.
--make_unbox_type :: CircuitType -> C.Type
--make_unbox_type (t,u) =
--  let t' = convert_qtype t
--      u' = convert_qtype u in
--  C.TypeAnnot 0 $ C.TArrow (C.TypeAnnot 0 $ C.TCirc t' u') (C.TypeAnnot 0 $ C.TArrow t' u')


-- | Return the types of all the occurences of \'unbox\' in the given expression.
--unbox_types :: C.Expr -> Compiler [C.Type]
--unbox_types (C.EFun _ _ e) =
--  unbox_types e

--unbox_types (C.EApp e f) = do
--  ue <- unbox_types e
--  uf <- unbox_types f
--  return $ List.unionBy C.equalsLinear ue uf

--unbox_types (C.ETuple _ elist) =
--  List.foldl (\rec e -> do
--        us <- rec
--        ue <- unbox_types e
--        return $ List.unionBy C.equalsLinear ue us) (return []) elist

--unbox_types (C.ELet _ _ e f) = do
--  ue <- unbox_types e
--  uf <- unbox_types f
--  return $ List.union ue uf

--unbox_types (C.EIf e f g) = do
--  ue <- unbox_types e
--  uf <- unbox_types f
--  ug <- unbox_types g
--  return $ List.unionBy C.equalsLinear ue $ List.union uf ug

--unbox_types (C.EDatacon _ _ (Just e)) =
--  unbox_types e

--unbox_types (C.EMatch e blist) = do
--  ue <- unbox_types e
--  ulist <- List.foldl (\rec (_, e) -> do
--        us <- rec
--        ue <- unbox_types e
--        return $ List.unionBy C.equalsLinear ue us) (return []) blist
--  return $ List.union ue ulist

--unbox_types (C.EUnbox ref) = do
--  ri <- ref_info ref
--  case ri of
--    Nothing ->
--        fail $ "PatternElimination:unbox_types: undefined reference: " ++ show ref
--    Just ri -> do
--        a <- map_type $ C.rtype ri
--        return [a]

--unbox_types (C.ECoerce e _) =
--  unbox_types e

--unbox_types _ =
--  return []


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
datacon_of_result :: TestResult -> Datacon
datacon_of_result (RDatacon d) = d
datacon_of_result _ = 0


-- | Build the list of the tests relevant to a pattern matching case, meaning all the tests that must
-- be checked true for the pattern matching case to be accepted.
-- TODO: tail rec implementation.
relevantTests :: C.Pattern -> Compiler [(TestLocation, TestResult)]
relevantTests pattern = relevantTestsAux [] pattern
  where
    -- The additional argument is the reversed location in the pattern.
    relevantTestsAux :: TestLocation -> C.Pattern -> Compiler [(TestLocation, TestResult)]
    relevantTestsAux location (C.PConstant _ (C.ConstInt _ n)) = return [(List.reverse location, RInt n)]
    relevantTestsAux location (C.PConstant _ (C.ConstBool _ b)) = return [(List.reverse location, RBool b)]
    relevantTestsAux location (C.PConstant _ (C.ConstUnit _)) = return []
    relevantTestsAux location (C.PWildcard _) = return []
    relevantTestsAux location (C.PVar _ _) = return []
    relevantTestsAux location (C.PDatacon _ cons arg) = do
      typ <- runCore $ getConstructorSourceType cons
      all <- allConstructors typ
      -- Sub-pattern tests.
      tests <-
        case args of
          Just pattern -> relevantTestsAux ((InDatacon cons):location) pattern
          Nothing -> return []
      -- Only one constructor: trivial pattern matching.
      -- Else add a test to check the constructor.
      if List.length all == 1 then return tests
      else do
        let test = [(List.reverse $ (InTag typ):location, RDatacon cons)]
        return $ test:tests
    relevantTestsAux location (C.PCoerce pattern _) = relevantTestsAux location pattern
    relevantTestsAux location (C.PTuple _ tuple) = do
      (_, tests) <- List.foldl (\rec (Binding binder value) -> do
          (i, tests) <- rec
          more <- relevantTestsAux ((InTuple i):location) binder
          return (i+1, more ++ tests)
        ) (return (0, [])) tuple
      return tests


-- | Build an optimized decision tree.
build_decision_tree :: [C.Pattern] -> Compiler DecisionTree
build_decision_tree plist = do
  -- Build the relevant tests first. Patterns are numbered from left to right, from 0 to n-1.
  -- For each test, the list of patterns for which it is relevant is added, along with the list of possible values.
  tset <- List.foldl (\rec (n,p) -> do
        tset <- rec
        tlist <- relevantTests p
        return $ List.foldl (\tset (test, result) ->
              case Map.lookup test tset of
                Nothing ->
                    Map.insert test [(n,result)] tset
                Just results ->
                    Map.insert test ((n, result):results) tset) tset tlist) (return Map.empty) (List.zip [0..(List.length plist)-1] plist)

  -- Build the decision tree upon the patterns remaining after the test defined by the given prefix.
  let build_tree = \tests patterns -> do
        case (tests, patterns) of
          -- Non-exhaustive pattern matching
          (_, []) -> return (Result (-1), [])
          -- One pattern has been identified
          ([], [n]) -> return (Result n, [])
          -- Redundency
          ([], n:ns) -> return (Result n, [])
          -- Undecided
          (t:ts, _) -> do
              -- Determine the test to do next, based on the relevance.
              let next = List.foldl (\(t, results) (t', results') ->
                    -- Test the validity of the comparison (always choose the shortest path).
                    if List.length t' < List.length t then
                      (t', results')
                    else if List.length t < List.length t' then
                      (t, results)
                    else
                      -- Compare the lowest relevant pattern
                      let min = List.minimum $ fst $ List.unzip results
                          min' = List.minimum $ fst $ List.unzip results' in
                      if min' < min then
                        (t', results')
                      else if min < min' then
                        (t, results)
                      else
                        -- If the previous test didn't work, compare the branching factor
                        let branching = List.length $ List.nub $ snd $ List.unzip results
                            branching' = List.length $ List.nub $ snd $ List.unzip results' in
                        if branching' < branching then
                          (t', results')
                        else
                          (t, results)) t ts

              -- Gather the possible results.
              results <- return $ List.nub $ snd $ List.unzip $ snd next
              results <- case List.head results of
                    -- If the result is a data constructor, all the possible results are the constructors from the same type.
                    RDatacon dcon -> do
                        typ <- datacon_datatype dcon
                        all <- all_data_constructors typ
                        -- If not all datacons are listed, add another result of the form ROtherDatacon.
                        if List.length results < List.length all then
                          return $ (ROtherDatacon $ List.map datacon_of_result results):results
                        else
                          return results
                    -- If the result is an integer, all the possible results are the ones listed here, plus the remaining integers in ROtherInt.
                    RInt _ ->
                       return $ (ROtherInt $ List.map intResult results):results
                    -- If the result is a boolean, check that both true and false are present
                    RBool _ ->
                       return [RBool True, RBool False]
                    _ ->
                       return results

              -- The remaining tests
              rtests <- return $ List.delete next tests

              -- Build the subtrees. At the same time, the list of unmatched cases is built.
              (subtrees, unmatched) <- List.foldl (\rec res -> do
                    (subtrees, unmatched) <- rec
                    -- List of the patterns matching this condition
                    patterns_ok <- return $ List.filter (\p ->
                          case List.lookup p (snd next) of
                            Just r -> r == res
                            -- This case corresponds to the patterns var and wildcard, that match everything
                            -- and yet are not relevant
                            Nothing -> True) patterns

                    -- List of the tests relevant for these patterns. Also, remove the uneeded results in each of the tests.
                    let relevantTests = List.filter (\(_, results) -> List.intersect (fst $ List.unzip results) patterns_ok /= []) rtests
                        relevantTests' = List.map (\(t, results) -> (t, List.filter (\(p, _) -> List.elem p patterns_ok) results)) relevantTests

                    -- If no test is relevant to the FIRST pattern, then it passes all the tests
                    case patterns_ok of
                      [] -> do
                          -- A pattern error
                          -- Build a sample pattern that corresponds to the unmatched case
                          let pcase = modify_pattern (plist !! List.head patterns) (fst next) res
                          -- Printing
                          fdata <- display_datacon
                          let prcase = genprint Inf [\_ -> "x", fdata] pcase
                          -- In case the expected result is 'ROtherInt' or 'ROtherDatacon', display the list of non-admissible integers as well
                          let prcase' =
                                case res of
                                  ROtherInt [i] ->
                                      prcase ++ " where x /= " ++ show i
                                  ROtherInt (i:is) ->
                                      prcase ++ " where x /= {" ++
                                      show i ++ List.foldl (\s i -> s ++ ", " ++ show i) "" is ++ "}"
                                  ROtherDatacon [d] ->
                                      prcase ++ " where x /= " ++ fdata d
                                  ROtherDatacon (d:ds) ->
                                      prcase ++ " where x /= {" ++
                                      fdata d ++ List.foldl (\s d -> s ++ ", " ++ fdata d) "" ds ++ "}"
                                  _ ->
                                      prcase
                          return ((res, Result (-1)):subtrees, prcase':unmatched)

                      n:_ -> do
                          -- Count the tests relevant to this particular pattern
                          rtests <- return $ List.filter (\(_, results) -> List.elem n $ fst $ List.unzip results) relevantTests'
                          if List.length rtests == 0 then
                            -- No need to take other tests
                            return ((res, Result n):subtrees, unmatched)
                          else do
                            -- Else, do the normal stuff
                            -- Build the subtree
                            (nsub, unmatched') <- build_tree relevantTests' patterns_ok
                            -- Return the rest
                            return ((res, nsub):subtrees, unmatched'++unmatched)) (return ([], [])) results

              -- Assemble the final tree
              return (Test (fst $ next) subtrees, unmatched)

  (tree, unmatched) <- build_tree (Map.assocs tset) [0..(List.length plist)-1]

  -- If unexhaustive match, send a warning
  let unmatched' = List.nub unmatched
  if unmatched' == [] then
    return ()
  else do
    ex <- get_location
    warnQ (UnexhaustiveMatch unmatched') ex

  -- Return the decision tree
  return tree

  where
      modify_pattern _ [] (ROtherInt ns) = C.PVar 0 0
      modify_pattern _ _ (ROtherDatacon ns) = C.PVar 0 0
      modify_pattern _ [] (RInt n) = C.PConstant 0 $ C.ConstInt n
      modify_pattern _ [] (RBool b) = C.PConstant 0 $ C.ConstBool b
      modify_pattern (C.PTuple r plist) ((InTuple n):ns) res =
        let plist' = List.map (\(m, p) ->
              if n == m then
                modify_pattern p ns res
              else
                p) (List.zip [0..List.length plist-1] plist) in
        C.PTuple r plist'
      modify_pattern (C.PDatacon r dcon (Just _)) [InTag _] (RDatacon dcon') =
        C.PDatacon r dcon' (Just $ C.PWildcard 0)
      modify_pattern (C.PDatacon r dcon Nothing) [InTag _] (RDatacon dcon') =
        C.PDatacon r dcon' Nothing
      modify_pattern (C.PDatacon r dcon (Just p)) ((InDatacon _):ns) res =
        let p' = modify_pattern p ns res in
        C.PDatacon r dcon (Just p')
      modify_pattern (C.PVar _ _) _ _ =
        C.PWildcard 0
      modify_pattern _ _ _ =
        throwNE $ ProgramError "PatternElimination:modify_pattern: illegal arguments"


-- | Extract the variables of a pattern, and return the sequence of functions applications necessary to retrieve them.
pattern_variables :: C.Pattern -> [(TestLocation, Variable)]
pattern_variables p =
  let read_vars = \loc p ->
        case p of
          C.PVar _ x -> [(List.reverse loc, x)]
          C.PDatacon _ dcon (Just p) ->
              read_vars ((InDatacon dcon):loc) p
          C.PCoerce p _ -> read_vars loc p
          C.PTuple _ plist ->
              List.foldl (\vars (n, p) ->
                            let vars' = read_vars ((InTuple n):loc) p in
                            vars' ++ vars) [] (List.zip [0..(List.length plist) -1] plist)
          _ -> []
        in
  read_vars [] p


-- | Find variable closest to the information one wants to extract.
longest_prefix :: [(TestLocation, Variable)] -> TestLocation -> (TestLocation, Variable, TestLocation)
longest_prefix extracted test =
  List.foldl (\(t, var, suf) (t', var') ->
        case List.stripPrefix t' test of
          Nothing -> (t, var, suf)
          Just suf' ->
              if List.length suf' <= List.length suf then
                (t', var', suf')
              else
                (t, var, suf)) ([], -1, test) extracted


-- | Complete the extraction of a piece of information. The argument should be the variable closest to the information we want to access.
-- The function then applies the operations necessary to go from this variable, to the information.
extractTest :: (TestLocation, Variable, TestLocation) -> Compiler (Expr -> Expr, [(TestLocation, Variable)], Variable)
extractTest (prefix, var, loc) =
  case loc of
    -- The variable 'var' already contains what we want
    [] -> return ((\e -> e), [], var)
    -- Else
    l:ls -> do
      -- Build some intermediary variables
      var' <- createVariable "x"
      exp <- case l of
            InTuple n ->
                return $ EAccess n var
            InDatacon dcon -> do
                getConstructorInfo dcon >>= extract >>= ($ var)
                --deconstruct <- datacon_def dcon >>= return . C.deconstruct
                --return $ deconstruct var
            InTag typ -> getTag typ var

      let nprefix = prefix ++ [l]
      (cont, updates, endvar) <- extractTest (nprefix, var', ls)
      return ((\e -> ELet var' exp $ cont e), (nprefix, var'):updates, endvar)


-- | Same as extract, except that the variable holding the information is specified beforehand.
extract_var :: (TestLocation, Variable, TestLocation) -> Variable -> Compiler (Expr -> Expr, [(TestLocation, Variable)])
extract_var (prefix, var, loc) endvar =
  case loc of
    -- The variable 'var' already contains what we want
    [] -> return ((\e -> ELet endvar (EVar var) e), [])
    -- The LAST action is a tuple accessor
    [InTuple n] -> return ((\e -> ELet endvar (EAccess n var) e), [])
    -- The LAST action is a destructor
    [InDatacon dcon] -> do
        extract <- getConstructorInfo dcon >> extract
        return ((\e -> ELet endvar (extract var) e), [])

    -- Else use an intermediary variable
    l:ls -> do
        var' <- createVariable "x"
        exp <- case l of
            InTuple n ->
                return $ EAccess n var
            InDatacon dcon -> do
                getConstructorInfo dcon >>= extract >>= ($ var)
                --deconstruct <- datacon_def dcon >>= return . C.deconstruct
                --return $ deconstruct var
            InTag typ -> getTag typ var

        nprefix <- return $ prefix ++ [l]
        (cont, updates) <- extract_var (nprefix, var', ls) endvar
        return ((\e -> ELet var' exp $ cont e), (nprefix, var'):updates)


-- | Using a decision tree, explain the tests that have to be done to compute a pattern matching.
simplify_pattern_matching :: C.Expr -> [(C.Pattern, C.Expr)] -> Compiler Expr
simplify_pattern_matching e blist = do
  patterns <- return $ fst $ List.unzip blist
  e' <- remove_patterns e
  dtree <- build_decision_tree patterns

  -- The 'extracted' argument associates locations in a pattern to variables.
  let unbuild = \dtree extracted ->
        case dtree of
          Result (-1) -> do
              return $ EError "Pattern Error"

          Result n -> do
              -- Get the list of the variables declared in the pattern
              (pn, en) <- return $ blist List.!! n
              vars <- return $ pattern_variables pn
              -- Remove the patterns from the expression en
              en' <- remove_patterns en
              -- Extract the variables from the pattern
              (initseq, _) <- List.foldl (\rec (loc, var) -> do
                    (cont, extracted) <- rec
                    (prefix, var', loc') <- return $ longest_prefix extracted loc
                    (cont', updates) <- extract_var (prefix, var', loc') var
                    return ((\e -> cont $ cont' e), updates ++ extracted)) (return ((\e -> e), extracted)) vars
              -- Allocate the variables, and build the final expression
              return $ initseq en'

          Test t results -> do
              (prefix, var, loc) <- return $ longest_prefix extracted t
              (initseq, updates, var') <- extract (prefix, var, loc)
              extracted <- return $ updates ++ extracted
              -- Build the sequence of tests
              teste <- case resultKind (fst $ List.unzip results) of
                    RInt _ -> do
                        -- Isolate the infinite case.
                        ([(_, remains)], others) <- return $ List.partition (\(r, _) ->
                              case r of
                                ROtherInt _ -> True
                                _ -> False) results
                        lastcase <- unbuild remains extracted
                        -- Eliminate the cases with the same results as the infinite case (= Result -1)
                        others <- return $ List.filter (\(res, subtree) ->
                              case subtree of
                                Result (-1) -> False
                                _ -> True) others

                        -- Build the conditions.
                        cases <- List.foldl (\rec (rint, subtree) -> do
                              n <- return $ case rint of {RInt n -> n; _ -> 0}
                              tests <- rec
                              testn <- unbuild subtree extracted
                              return $ (n, testn):tests) (return []) others

                        -- Build the completed expression.
                        return $ EMatch (EVar var') cases lastcase

                    RBool _ -> do
                        rtrue <- case List.lookup (RBool True) results of
                              Just t -> return t
                              Nothing -> fail "PatternElimination:simplify_pattern_matching: missing case True"
                        rfalse <- case List.lookup (RBool False) results of
                              Just t -> return t
                              Nothing -> fail "PatternElimination:simplify_pattern_matching: missing case False"
                        casetrue <- unbuild rtrue extracted
                        casefalse <- unbuild rfalse extracted
                        return $ EMatch (EVar var') [(1,casetrue)] casefalse

                    RDatacon _ -> do
                        -- Isolate the default (ROtherDatacon) case (if one exists).
                        let (remain, others) = List.foldl (\(remain, others) (r, subtree) ->
                              case r of
                                ROtherDatacon _ -> (Just (r,subtree), others)
                                _ -> (remain, (r,subtree):others) ) (Nothing, []) results
                        -- Build the standard cases.
                        cases <- List.foldl (\rec (rdcon, subtree) -> do
                              cases <- rec
                              tag <- case rdcon of
                                    RDatacon dcon -> getConstructorInfo dcon >> tag
                                    --datacon_def dcon >>= return . C.tag
                                    _ -> return (-1)
                              e <- unbuild subtree extracted
                              return $ (tag, e):cases) (return []) others
                        -- Build the default case.
                        case remain of
                          Nothing ->
                              return $ EMatch (EVar var') (List.init cases) $ snd $ List.last cases
                          Just (_, subtree) -> do
                              e <- unbuild subtree extracted
                              return $ EMatch (EVar var') cases e

                    ROtherInt _ ->
                        fail "PatternElimination:simplify_pattern_matching: unexpected result 'ROtherInt'"
                    ROtherDatacon _ ->
                        fail "PatternElimination:simplify_pattern_matching: unexpected result 'ROtherDatacon'"

              -- Complete the sequence with the variable extraction
              return $ initseq teste

  -- If the test expression is not a variable, then push it in a variable
  case e' of
    EVar iniTypeVar -> do
        unbuild dtree [([], iniTypeVar)]
    _ -> do
        iniTypeVar <- createVariable "x"
        tests <- unbuild dtree [([], iniTypeVar)]
        return $ ELet iniTypeVar e' tests



-- | Remove the patterns. Some are left in the match expressions, but should only be of the form @A _@ or @_@, where @_@ is the wildcard.
remove_patterns :: C.Expr -> Compiler Expr
remove_patterns (C.EVar _ x) =
  return $ EVar x

remove_patterns (C.EGlobal _ x) = do
  return $ EGlobal x

remove_patterns (C.EFun ref p e) = do
   -- Check whether the expression is already  or not
  case p of
    -- The pattern is only one variable: do nothing
    C.PVar _ x -> do
      e' <- remove_patterns e
      return $ EFun x e'

    -- The pattern is the wildcard: do nothing (except from creating a variable for the argument).
    C.PWildcard _ -> do
      e' <- remove_patterns e
      x <- createVariable "x"
      return $ EFun x e'

    -- If the pattern is more complicated, replace it by a variable
    _ -> do
      x <- createVariable "x"
      e' <- remove_patterns $ C.ELet Nonrecursive p (C.EVar 0 x) e
      return $ EFun x e'

remove_patterns (C.EApp e f) = do
  e' <- remove_patterns e
  f' <- remove_patterns f
  return $ EApp e' f'

remove_patterns (C.ETuple _ elist) = do
  elist' <- List.foldl (\rec e -> do
        es <- rec
        e' <- remove_patterns e
        return $ e':es) (return []) elist
  return $ ETuple $ List.reverse elist'

-- Intercept recursive functions.
remove_patterns (C.ELet Recursive (C.PVar _ v) e f) = do
  e' <- remove_patterns e
  f' <- remove_patterns f
  case e' of
    EFun x e ->
        return $ ELet v (EFix v x e) f'
    _ ->
        fail "PatternElimination:remove_patterns: unexpected recursive object"

remove_patterns (C.ELet _ (C.PVar _ v) e f) = do
  e' <- remove_patterns e
  f' <- remove_patterns f
  return $ ELet v e' f'

remove_patterns (C.ELet r (C.PWildcard _) e f) = do
  e' <- remove_patterns e
  f' <- remove_patterns f
  return $ ESeq e' f'

remove_patterns (C.ELet Nonrecursive p e f) = do
  remove_patterns (C.EMatch e [(p, f)])

remove_patterns (C.ELet Recursive _ _ _) =
  fail "PatternElimination:remove_patterns: unexpected recursive binding"

remove_patterns (C.EConstant _ c) = return $ EConstant c

remove_patterns (C.EIf e f g) = do
  e' <- remove_patterns e
  f' <- remove_patterns f
  g' <- remove_patterns g
  return $ EMatch e' [(1,f')] g'

remove_patterns (C.EDatacon _ dcon Nothing) = do
  ddef <- getConstructorInfo dcon
  -- If the data constructor expected an argument, then return a pointer to an implementation
  -- of the incomplete constructor.
  if implementation ddef == -1 then do
    Left build <- getConstructorInfo dcon >> build
    return build
  else
    return $ EGlobal $ implementation ddef

remove_patterns (C.EDatacon _ dcon (Just e)) = do
  Right build <- getConstructorInfo dcon >> build
  e' <- remove_patterns e
  return $ build e'

remove_patterns (C.EMatch e blist) = do
  simplify_pattern_matching e blist

remove_patterns (C.EBox _ typ) = do
  typ <- C.quantumTypeOfType typ
  x <- request_box typ
  return (EVar x)

remove_patterns (C.EUnbox ref) = do
  ri <- ref_info_err ref
  let typ = C.rtype ri
  typ <- map_type typ
  (t, u) <- C.circuitTypeOfType typ
  -- Check the type of the unbox operator
  if not (is_concrete t && is_concrete u) then do
    warnQ (AmbiguousUnbox) (C.extent ri)
    return $ EInt 0
  else do
    x <- request_unbox (t,u)
    return (EVar x)

remove_patterns (C.ERev _) = do
  x <- request_rev
  return (EVar x)

remove_patterns (C.ECoerce e t) =
  remove_patterns e

remove_patterns (C.EError msg) =
  return (EError msg)


-- | Modify the body of a module by applying the function 'disambiguate_unbox_calls' and 'remove_pattern'
-- to all the top-level declarations.
transform_declarations :: [C.Declaration] -> Compiler [Declaration]
transform_declarations decls = do
  (decls, _) <- List.foldl (\rec d -> do
        (decls, mod) <- rec
        case d of
          C.DExpr e -> do
              warnQ NakedExpressionToplevel extent_unknown
              return (decls, mod)

          C.DLet recflag x e -> do
              -- DISAMBIGUATION
              -- First disambiguate the calls from e
              e' <- disambiguate_unbox_calls [] mod e

              -- Then pick up the remaining unbox calls
              need <- unbox_types e'
              need <- return $ List.filter (\a -> not $ C.isConcrete a) need

              -- Unresolved unbox operators
              if need /= [] then do
                typ <- global_type x >>= return . C.typeOfScheme

                -- Specify the calling convention for x
                set_call_convention x need

                -- Add the variable and its (new) arguments to the mod context
                let mod' = IMap.insert x (typ, need) mod

                -- Add new argument variables to the arg context
                args <- List.foldr (\a rec -> do
                      as <- rec
                      v <- createVariable "u"
                      return $ (a, v):as) (return []) need

                -- Disambiguate the calls from e again
                e' <- disambiguate_unbox_calls args mod' e

                -- Transform e' into a function
                let e'' = List.foldl (\e (_, v) -> C.EFun 0 (C.PVar 0 v) e) e' args

                -- Remove the patterns
                e'' <- remove_patterns e''
                case (recflag, e'') of
                  (Recursive, EFun v e) -> return ((DLet External x $ EFix x v e):decls, mod')
                  _ -> return ((DLet External x e''):decls, mod')

              -- No unresolved unbox operators.
              else do
                e' <- remove_patterns e
                case (recflag, e') of
                  -- Recursive function.
                  (Recursive, EFun v e) -> return ((DLet External x $ EFix x v e):decls, mod)
                  -- Function.
                  (Nonrecursive, EFun v e) -> return ((DLet External x $ EFun v e):decls, mod)
                  _ -> do
                      typ <- global_type x >>= return . C.typeOfScheme
                      if isFunction typ then do
                        -- Necessary eta-expansion.
                        a <- createVariable "x"
                        return ((DLet External x $ EFun a (EApp e' $ EVar a)):decls, mod)
                      else
                        return ((DLet External x e'):decls, mod)

      ) (return ([], IMap.empty)) decls

  -- Retrieve the declaration of quantum operations
  qops <- clear_circuit_ops

  return $ qops ++ List.reverse decls



{-# LANGUAGE ScopedTypeVariables #-}

{- | This module implements the first step of the compilation, where all the patterns are removed.
Among the methods used to remove the patterns, there is :

* In the pattern matchings, the nth element of a tuple is accessed through the builtin functions #1, #2, ..

* In the pattern matchings, the element of a data constructor is accessed through automatically generated destructors (or projections). For example,
the value @a@ contained in @Right a@ is accessed via @proj_Right (Right a)@.

* The case expressions are reduced to the simplest form (only one case at a time).

In the process, new builtin operations are defined :

* PATTERN_ERROR : that generates an error when a pattern matching fails.

* #1, #2 ...    : tuple accessors.

Note that the type constraints and location information are also removed.
-}

module Compiler.PatternRemoval where

import Classes
import Utils

import Monad.QpState
import Monad.QuipperError

import Parsing.Syntax (RecFlag(..))
import qualified Parsing.Syntax as S

import Typing.CoreSyntax (Variable, Datacon)
import qualified Typing.CoreSyntax as C

import Control.Exception

import Text.PrettyPrint.HughesPJ as PP

import qualified Data.List as List
import qualified Data.Map as Map

-- | Definition of a set of expressions, where patterns have been removed.
data Expr =
-- STLC
    EVar Variable                                 -- ^ Variable: /x/.
  | EGlobal Variable                              -- ^ Global variable from the imported modules.
  | EFun Variable Expr                            -- ^ Function abstraction: @fun x -> t@.
  | EApp Expr Expr                                -- ^ Function application: @t u@.

-- Introduction of the tensor
  | EUnit                                         -- ^ Unit term: @()@.
  | ETuple [Expr]                                 -- ^ Tuple: @(/t/1, .. , /t//n/)@. By construction, must have /n/ >= 2.
  | ELet RecFlag Variable Expr Expr               -- ^ Let-binding: @let [rec] p = e in f@.
  | ESeq Expr Expr                                -- ^ The expression @e; f@, semantically equivalent to @let _ = e in f@.

-- Custom union types
  | EBool Bool                                    -- ^ Boolean constant: @true@ or @false@.
  | EInt Int                                      -- ^ Integer constant.
  | EIf Expr Expr Expr                            -- ^ Conditional: @if e then f else g@.
  | EDatacon Datacon (Maybe Expr)                 -- ^ Data constructor: @Datacon e@. The argument is optional. The data constructors are considered and manipulated as values.
  | EMatch Expr [(Datacon, Expr)]                 -- ^ Case distinction: @match e with (p1 -> f1 | .. | pn -> fn)@.

-- Quantum rules
  | EBox Int                                      -- ^ The constant @box[T]@. The type annotation is replaced by a integer indicating the number of input qubits.
  | EUnbox                                        -- ^ The constant @unbox@.
  | ERev                                          -- ^ The constant @rev@.

-- Unrelated
  | EBuiltin String                               -- ^ Built-in primitive: @#builtin s@.
  deriving Show



-- | Return the name of the builtin function returning the nth element of a tuple.
nth_accessor :: Int -> Expr
nth_accessor n =
  EBuiltin ("#" ++ show n)


-- | Representation of a decision tree, that decides which test to do first in order to minimize the number of comparisons.
data DecisionTree =
    Test [TestLocation] [(TestResult, DecisionTree)]         -- ^ Test the nth element of a tuple (a boolean). Depending on the result, different tests are taken.
  | Result Int                                               -- ^ The number of the matched pattern.
  deriving Show

-- | Position of the information relevant to a test.
data TestLocation =
    InTuple Int        -- ^ The information is the Nth element of a tuple.
  | InDatacon Datacon  -- ^ The information is the argument of a data constructor.
  deriving (Show, Eq, Ord)


-- | The result of a test.
data TestResult =
    RInt Int                -- ^ The result of the test is an integer.
  | RRemainInt              -- ^ As a matching on integers is never complete, this constructor stands for all the integers not present in the test patterns.
  | RBool Bool              -- ^ The result is a boolean.
  | RDatacon Datacon        -- ^ The result is a data constructor.
  deriving (Show, Eq)

-- | Return the kind of a list of results. It is typically an example from the list.
rkind :: [TestResult] -> TestResult
rkind [] =
  error "rkind: empty list"
rkind (RInt _:_) = RInt 0
rkind (RRemainInt:_) = RInt 0
rkind (RBool _:_) = RBool True
rkind (RDatacon _:_) = RDatacon 0


-- | Build the list of the tests relevant to a pattern. The result of the test is returned each time.
relevant_tests :: C.Pattern -> QpState [([TestLocation], TestResult)]
relevant_tests p =
  -- The location in the pattern is passed as argument here (reversed though).
  let ptests = \ns p ->
        case p of
          C.PInt n -> return [(List.reverse ns, RInt n)]
          C.PBool b -> return [(List.reverse ns, RBool b)]
          C.PUnit -> return []
          C.PWildcard -> return []
          C.PVar _ -> return []
          C.PDatacon dcon Nothing -> do
              typ <- datacon_type dcon
              all <- all_data_constructors typ
              if List.length all == 1 then
                return []
              else
                return [(List.reverse ns, RDatacon dcon)]
          C.PDatacon dcon (Just p) -> do
              typ <- datacon_type dcon
              all <- all_data_constructors typ
              if List.length all == 1 then
                ptests ((InDatacon dcon):ns) p
              else do
                tset <- ptests ((InDatacon dcon):ns) p
                return $ (List.reverse ns, RDatacon dcon):tset
          C.PLocated p _ -> ptests ns p
          C.PConstraint p _ -> ptests ns p
          C.PTuple plist ->
              List.foldl (\rec (n, p) -> do
                            tset <- rec
                            tset' <- ptests ((InTuple n):ns) p
                            return $ tset' ++ tset) (return []) (List.zip [0..(List.length plist) -1] plist)
        in
  ptests [] p


-- | Build an optimized decision tree.
build_decision_tree :: [C.Pattern] -> QpState DecisionTree
build_decision_tree plist = do
  -- Build the relevant tests first. Patterns are numbered from left to right, from 0 to n-1.
  -- For each test, the list of patterns for which it is relevant is added, along with the list of possible values.
  tset <- List.foldl (\rec (n,p) -> do
          tset <- rec
          tlist <- relevant_tests p
          return $ List.foldl (\tset (test, result) ->
                  case Map.lookup test tset of
                    Nothing ->
                        Map.insert test [(n,result)] tset
                    Just results ->
                        Map.insert test ((n, result):results) tset) tset tlist) (return Map.empty) (List.zip [0..(List.length plist)-1] plist)
  
  -- Build the decision tree upon the patterns remaining after the test defined by the given prefix.
  build_tree <- return (let build_tree = \tests patterns -> do
                            case (tests, patterns) of
                              -- Non-exhaustive pattern matching
                              (_, []) -> return $ Result (-1)
                              -- One pattern has been identified
                              ([], [n]) -> return $ Result n
                              -- Redundency
                              ([], n:ns) -> return $ Result n

                              (t:ts, _) -> do
                                  -- Determine the test to do next, based on the relevance.
                                  next <- return $ List.foldl (\(t, results) (t', results') ->
                                                           -- Test the validity of the comparison (can't test 1.2.3 before 1.2)
                                                           if List.isPrefixOf t' t then
                                                             (t', results')
                                                           else if List.isPrefixOf t t' then
                                                             (t, results)
                                                           else
                                                             let min = List.minimum $ fst $ List.unzip results
                                                                 min' = List.minimum $ fst $ List.unzip results' in
                                                             -- Compare the lowest relevant pattern
                                                             if min' < min then
                                                               (t', results')
                                                             else if min < min' then
                                                               (t, results)
                                                             else
                                                               let branching = List.length $ List.nub $ snd $ List.unzip results
                                                                   branching' = List.length $ List.nub $ snd $ List.unzip results' in
                                                               -- If the previous test didn't work, compare the branching factor
                                                               if branching' < branching then
                                                                 (t', results')
                                                               else
                                                                 (t, results)) t ts

                                  -- Gather the possible results.
                                  results <- return $ List.nub $ snd $ List.unzip $ snd next
                                  results <- case List.head results of
                                               -- If the result is a data constructor, all the possible results are the constructors from the same type.
                                               RDatacon dcon -> do
                                                  typ <- datacon_type dcon
                                                  all <- all_data_constructors typ
                                                  return $ List.map (\dcon -> RDatacon dcon) all
                                               -- If the result is an integer, all the possible results are the ones listed here, plus the remaining integers in RRemainInt.
                                               RInt _ ->
                                                   return $ RRemainInt:results
                                               -- If the result is a boolean, check that both true and false are present
                                               RBool _ ->
                                                   return [RBool True, RBool False]
                                               _ ->
                                                   return results
                                  
                                  -- The remaining tests
                                  rtests <- return $ List.delete next tests

                                  -- Build the subtress
                                  subtrees <- List.foldl (\rec res -> do
                                                             subtrees <- rec
                                                             -- List of the patterns matching this condition
                                                             patterns_ok <- return $ List.filter (\p -> case List.lookup p (snd next) of
                                                                                                    Just r -> r == res
                                                                                                    -- This case corresponds to the patterns var and wildcard, that matches everything
                                                                                                    -- and yet are not relevant
                                                                                                    Nothing -> True) patterns
                                                             -- List of the tests relevant on these patterns
                                                             relevant_tests <- return $ List.filter (\(_, results) -> List.intersect (fst $ List.unzip results) patterns_ok /= []) rtests
                                                             -- Build the subtree
                                                             nsub <- build_tree relevant_tests patterns_ok
                                                             -- Return the rest
                                                             return $ (res, nsub):subtrees) (return []) results
                  
                                  -- Assemble the final tree
                                  return $ Test (fst $ next) subtrees in
                                build_tree)

  build_tree (Map.assocs tset) [0..(List.length plist)-1]


-- | Extract the variables of a pattern, and return the sequence of functions applications necessary to retrieve them.
pattern_variables :: C.Pattern -> [([TestLocation], Variable)]
pattern_variables p =
  let read_vars = \loc p ->
        case p of
          C.PVar x -> [(List.reverse loc, x)]
          C.PDatacon dcon (Just p) ->
              read_vars ((InDatacon dcon):loc) p
          C.PLocated p _ -> read_vars loc p
          C.PConstraint p _ -> read_vars loc p
          C.PTuple plist ->
              List.foldl (\vars (n, p) ->
                            let vars' = read_vars ((InTuple n):loc) p in
                            vars' ++ vars) [] (List.zip [0..(List.length plist) -1] plist)
          _ -> []
        in
  read_vars [] p



-- | Using a decision tree, explain the tests that have to be done to compute a pattern matching.
simplify_pattern_matching :: C.Expr -> [(C.Pattern, C.Expr)] -> QpState Expr
simplify_pattern_matching e blist = do
  patterns <- return $ fst $ List.unzip blist
  e' <- remove_patterns_in_expr e
  dtree <- build_decision_tree patterns
  
  -- Return the longest prefix of a test location.
  longest_prefix <- return $ \(extracted :: [([TestLocation], Variable)]) (test :: [TestLocation]) ->
                                  List.foldl (\(t, var, suf) (t', var') ->
                                                case List.stripPrefix t' test of
                                                  Nothing -> (t, var, suf)
                                                  Just suf' ->
                                                    if List.length suf' < List.length suf then
                                                      (t', var', suf')
                                                    else
                                                      (t, var, suf)) ([], -1, test) extracted

  -- Complete the extraction of a piece of information
  -- In the arguments : var is the starting point, loc the series of instructions.
  -- In the return value : the first argument is a series of variable allocation, the second contains the updates of the extracted variables,
  -- the third is the variable holding the information.
  extract <- return (let extract = \(prefix, var, loc) ->
                                   case loc of
                                     [] -> return ([], [], var)
                                     l:ls -> do
                                         var' <- dummy_var
                                         exp <- return $ EApp (case l of
                                                                 InTuple n -> nth_accessor n
                                                                 InDatacon _ -> EBuiltin "EXTRACT") (EVar var)
                                         nprefix <- return $ prefix ++ [l]
                                         (exps, updates, endvar) <- extract (nprefix, var', ls)
                                         return ((var', exp):exps, (nprefix, var'):updates, endvar)
                                    in
                     extract)

  -- Same as extract, except that the variable holding the information is specified beforehand.
  extract_var <- return (let extract_var = \(prefix, var, loc) endvar -> do
                                     case loc of
                                       [] -> return ([(endvar, EVar var)], [])
                                       [InTuple n] -> return ([(endvar, EApp (nth_accessor n) (EVar var))], [])
                                       [InDatacon _] -> return ([(endvar, EApp (EBuiltin "EXTRACT") (EVar var))], [])
                                       l:ls -> do
                                           var' <- dummy_var
                                           exp <- return $ EApp (case l of
                                                                   InTuple n -> nth_accessor n
                                                                   InDatacon _ -> EBuiltin "EXTRACT") (EVar var)
                                           nprefix <- return $ prefix ++ [l]
                                           (exps, updates) <- extract_var (nprefix, var', ls) endvar
                                           return ((var',exp):exps, (nprefix, var'):updates)
                                     in
                     extract_var)
                         

  -- The 'extracted' argument associates locations in a pattern to variables.
  unbuild <- return (let unbuild = \dtree extracted ->
                            case dtree of
                              Result (-1) ->
                                  return $ EBuiltin "PATTERN_ERROR"

                              Result n -> do
                                  -- Get the list of the variables declared in the pattern
                                  (pn, en) <- return $ blist List.!! n
                                  vars <- return $ pattern_variables pn
                                  -- Remove the patterns from the expression en
                                  en' <- remove_patterns_in_expr en
                                  -- Extract the variables from the pattern
                                  (exps, _) <- List.foldl (\rec (loc, var) -> do
                                                        (exps, extracted) <- rec
                                                        (prefix, var', loc') <- return $ longest_prefix extracted loc
                                                        (exps', updates) <- extract_var (prefix, var', loc') var
                                                        return (exps ++ exps', updates ++ extracted)) (return ([], extracted)) vars
                                  -- Allocate the variables, and build the final expression
                                  List.foldr (\(var, exp) rec -> do
                                                e <- rec
                                                return $ ELet Nonrecursive var exp e) (return en') exps

                              Test t results -> do
                                  (prefix, var, loc) <- return $ longest_prefix extracted t
                                  (exps, updates, var') <- extract (prefix, var, loc)
                                  extracted <- return $ updates ++ extracted
                                  -- Build the sequence of tests
                                  teste <- case rkind (fst $ List.unzip results) of
                                             RInt _ -> do 
                                                 -- Isolate the infinite case, and put it at the end of the list
                                                 ([(_, remains)], others) <- return $ List.partition (\(r, _) -> case r of
                                                                                                  RRemainInt -> True
                                                                                                  _ -> False) results
                                                 lastcase <- unbuild remains extracted
                                                 -- Build the if conditions
                                                 List.foldl (\rec (rint, subtree) -> do
                                                               n <- return $ case rint of {RInt n -> n; _ -> 0}
                                                               tests <- rec
                                                               testn <- unbuild subtree extracted
                                                               return $ EIf (EApp (EApp (EBuiltin "EQ") (EVar var')) (EInt n))
                                                                            testn
                                                                            tests) (return lastcase) others
     
                                             RBool _ -> do
                                                 rtrue <- case List.lookup (RBool True) results of
                                                            Just t -> return t
                                                            Nothing -> throwQ $ ProgramError "Missing boolean cases in pattern matching"
                                                 rfalse <- case List.lookup (RBool False) results of
                                                            Just t -> return t
                                                            Nothing -> throwQ $ ProgramError "Missing boolean cases in pattern matching"
                                                 casetrue <- unbuild rtrue extracted
                                                 casefalse <- unbuild rfalse extracted
                                                 return $ EIf (EVar var') casetrue casefalse

                                             RDatacon _ -> do
                                                 cases <- List.foldl (\rec (rdcon, subtree) -> do
                                                                         dcon <- return $ case rdcon of {RDatacon dcon -> dcon; _ -> 0}
                                                                         cases <- rec
                                                                         e <- unbuild subtree extracted
                                                                         return $ (dcon, e):cases) (return []) results
                                                 return $ EMatch (EVar var') cases

                                             RRemainInt ->
                                                 throwQ $ ProgramError "Unexpected result 'RRemainInt'"

                                  -- Complete the sequence with the variable extraction
                                  List.foldr (\(var, exp) rec -> do
                                                e <- rec
                                                return $ ELet Nonrecursive var exp e) (return teste) exps
                              in
                            unbuild)

  -- If the test expression is not a variable, then push it in a variable
  case e' of
    EVar initvar -> do
        unbuild dtree [([], initvar)]
    _ -> do
        initvar <- dummy_var
        tests <- unbuild dtree [([], initvar)]
        return $ ELet Nonrecursive initvar e' tests



-- | Remove the patterns. Some are left in the match expressions, but should only be of the form @A _@ or @_@, where @_@ is the wildcard.
remove_patterns_in_expr :: C.Expr -> QpState Expr
remove_patterns_in_expr (C.EVar x) =
  return $ EVar x

remove_patterns_in_expr (C.EGlobal x) =
  return $ EGlobal x

remove_patterns_in_expr (C.EFun p e) = do
   -- Check whether the expression is already  or not
  case p of
    -- The pattern is only one variable: do nothing
    C.PVar x -> do
      e' <- remove_patterns_in_expr e
      return $ EFun x e'

    -- If the pattern is more complicated, replace it by a variable
    _ -> do
      x <- dummy_var
      e' <- remove_patterns_in_expr $ C.ELet Nonrecursive p (C.EVar x) e
      return $ EFun x e'

remove_patterns_in_expr (C.EApp e f) = do
  e' <- remove_patterns_in_expr e
  f' <- remove_patterns_in_expr f
  return $ EApp e' f'

remove_patterns_in_expr C.EUnit = do
  return EUnit

remove_patterns_in_expr (C.ETuple elist) = do
  elist' <- List.foldl (\rec e -> do
                          es <- rec
                          e' <- remove_patterns_in_expr e
                          return $ e':es) (return []) elist
  return $ ETuple elist'

remove_patterns_in_expr (C.ELet r p e f) = do
  e' <- remove_patterns_in_expr e
  case p of
    -- If the pattern is unit
    C.PUnit -> do
        f' <- remove_patterns_in_expr f
        return $ ESeq e' f'

    -- If the pattern is boolean
    (C.PBool b) -> do
        f' <- remove_patterns_in_expr f
        return $ if b then
                   EIf e' f' (EBuiltin "PATTERN_ERROR")
                 else 
                   EIf e' (EBuiltin "PATTERN_ERROR") f'

    -- If the pattern is an integer: do nothing
    (C.PInt n) -> do
        f' <- remove_patterns_in_expr f
        x <- dummy_var
        return $ ELet r x f' (
                   EIf (EApp (EApp (EBuiltin "EQ") (EInt n)) (EVar x)) f' (EBuiltin "PATTERN_ERROR"))

    -- If the pattern is one variable, do nothing
    -- The let binding can't be removed because of let-polymorphism
    C.PVar x -> do
        f' <- remove_patterns_in_expr f
        return $ ELet r x e' f'

    -- If the pattern is a pair of variables, this is the case of tensor elimination
    C.PTuple plist -> do
        -- The tuple will be saved in that variable
        xp <- dummy_var
        -- For each element of the tuple, the variable is extracted using #1 #2 ..
        (_,f) <- List.foldl (\rec p -> do
                               (n, e) <- rec
                               return (n+1, C.ELet r p (C.EApp (C.EBuiltin $ "#" ++ show n) (C.EVar xp)) e)) (return (0, f)) plist
        e' <- remove_patterns_in_expr e
        f' <- remove_patterns_in_expr f
        return $ ELet r xp e' f'

    -- If the pattern is a datacon, remove_patterns_in_expr by adding a pattern matching
    C.PDatacon dcon Nothing -> do
        f' <- remove_patterns_in_expr f
        return $ EMatch e' [(dcon, f')]

    C.PDatacon dcon (Just p) -> do
        x <- dummy_var
        ep <- remove_patterns_in_expr (C.ELet Nonrecursive p (C.EApp (C.EBuiltin "EXTRACT") (C.EVar x)) f)
        return $ ELet Nonrecursive x e' (
                   EMatch (EVar x) [(dcon, ep)]
                 )
    -- The wildcard
    C.PWildcard -> do
        f' <- remove_patterns_in_expr f
        return $ ESeq e' f'

    -- Others
    C.PLocated _ _ ->
        throwQ $ ProgramError "Located patterns remaining"
    C.PConstraint _ _ ->
        throwQ $ ProgramError "Constraint remaining in pattern"

remove_patterns_in_expr (C.EBool b) = do
  return $ EBool b

remove_patterns_in_expr (C.EInt n) = do
  return $ EInt n

remove_patterns_in_expr (C.EIf e f g) = do
  e' <- remove_patterns_in_expr e
  f' <- remove_patterns_in_expr f
  g' <- remove_patterns_in_expr g
  return $ EIf e' f' g'

remove_patterns_in_expr (C.EDatacon dcon Nothing) = do
  return $ EDatacon dcon Nothing

remove_patterns_in_expr (C.EDatacon dcon (Just e)) = do
  e' <- remove_patterns_in_expr e
  return $ EDatacon dcon $ Just e'

remove_patterns_in_expr (C.EMatch e blist) = do
  simplify_pattern_matching e blist

remove_patterns_in_expr (C.EBox typ) = do
  return $ EBox 0

remove_patterns_in_expr C.EUnbox = do
  return EUnbox

remove_patterns_in_expr C.ERev = do
  return ERev

remove_patterns_in_expr (C.ELocated e ex) = do
  remove_patterns_in_expr e

remove_patterns_in_expr (C.EBuiltin s) =
  return (EBuiltin s)
  
remove_patterns_in_expr (C.EConstraint e t) =
  remove_patterns_in_expr e



-- | Merge the declarations of a code file.
-- Variable declarations are handled as in :
--
-- @
--   let p = e;
--   f
-- @
--
-- which gives
--
-- @
--  let x1 = e1 in
--  let x2 = e2 in
--  ..
--  f
-- @
--
-- where x1, x2.. are the variables declared in the pattern @p@.
-- Top level expressions cannot be readily removed, because of possible side effects on the circuit stack ; they
-- are instead replaced by :
-- 
-- @
--   let _ = e in
--   ..
-- @
--
-- where @_@ is the wildcard, and @e@ the top level expression.
merge_declarations :: [S.Declaration] -> QpState Expr
merge_declarations _ = return EUnit



-- * Printing functions.

-- | Pretty-print an expression using Hughes's and Peyton Jones's
-- pretty printer combinators. The type 'Doc' is defined in the library
-- "Text.PrettyPrint.HughesPJ" and allows for nested documents.
print_doc :: Lvl                   -- ^ Maximum depth.
          -> Expr                  -- ^ Expression to print.
          -> (Variable -> String)  -- ^ Rendering of term variables.
          -> (Variable -> String)  -- ^ Rendering of data constructors.
          -> Doc                   -- ^ Resulting PP document.
print_doc _ EUnit _ _ =
  text "()"

print_doc _ (EBool b) _ _ = 
  if b then text "true" else text "false"

print_doc _ (EInt n) _ _ =
  text $ show n

print_doc _ (EVar x) fvar _ = text $ fvar x

print_doc _ (EGlobal x) fvar _ = text $ fvar x

print_doc _ (EBox n) _ _=
  text "box" <> brackets (text $ show n)

print_doc _ EUnbox _ _ =
  text "unbox"

print_doc _ ERev _ _ =
  text "rev"

print_doc _ (EDatacon datacon Nothing) _ fdata =
  text $ fdata datacon

print_doc _ (EBuiltin s) _ _=
  text "#builtin" <+> text s

print_doc (Nth 0) _ _ _ =
  text "..."

print_doc lv (ESeq e f) fvar fdata =
  (print_doc lv e fvar fdata) <+> text ";" $$
  (print_doc lv f fvar fdata)

print_doc lv (ELet r v e f) fvar fdata =
  let dlv = decr lv in
  let recflag = if r == Recursive then text "rec" else empty in
  text "let" <+> recflag <+> text (fvar v) <+> equals <+> print_doc dlv e fvar fdata <+> text "in" $$
  print_doc dlv f fvar fdata

print_doc lv (ETuple elist) fvar fdata =
  let dlv = decr lv in
  let plist = List.map (\e -> print_doc dlv e fvar fdata) elist in
  let slist = punctuate comma plist in
  char '(' <> hsep slist <> char ')'

print_doc lv (EApp e f) fvar fdata =
  let dlv = decr lv in
  let pe = print_doc dlv e fvar fdata
      pf = print_doc dlv f fvar fdata in
  (case e of
     EFun _ _ -> parens pe
     _ -> pe) <+> 
  (case f of
     EFun _ _ -> parens pf
     EApp _ _ -> parens pf
     _ -> pf)

print_doc lv (EFun v e) fvar fdata =
  let dlv = decr lv in
  text "fun" <+> text (fvar v) <+> text "->" $$
  nest 2 (print_doc dlv e fvar fdata)

print_doc lv (EIf e f g) fvar fdata =
  let dlv = decr lv in
  text "if" <+> print_doc dlv e fvar fdata <+> text "then" $$
  nest 2 (print_doc dlv f fvar fdata) $$
  text "else" $$
  nest 2 (print_doc dlv g fvar fdata)

print_doc lv (EDatacon datacon (Just e)) fvar fdata =
  let pe = print_doc (decr lv) e fvar fdata in
  text (fdata datacon) <+> (case e of
                              EBool _ -> pe
                              EUnit -> pe
                              EVar _ -> pe
                              _ -> parens pe)

print_doc lv (EMatch e blist) fvar fdata =
  let dlv = decr lv in
  text "match" <+> print_doc dlv e fvar fdata <+> text "with" $$
  nest 2 (List.foldl (\doc (p, f) ->
                        let pmatch = char '|' <+> text (genprint dlv p [fvar, fdata]) <+> text "->" <+> print_doc dlv f fvar fdata in
                        if isEmpty doc then
                          pmatch
                        else
                          doc $$ pmatch) PP.empty blist)



-- | Printing of expressions. The function 'genprint' generalizes the display of term
-- variables and data constructors.
instance PPrint Expr where
  -- Generic printing
  genprint lv e [fvar, fdata] =
    let doc = print_doc lv e fvar fdata in
    PP.render doc
  genprint lv e _ =
    throw $ ProgramError "Expr:genprint: illegal argument"

  -- Other
  -- By default, the term variables are printed as x_n and the data constructors as D_n,
  -- where n is the id of the variable / constructor
  sprintn lv e = genprint lv e [subvar 'x', subvar 'D']
  sprint e = sprintn defaultLvl e
  pprint e = sprintn Inf e





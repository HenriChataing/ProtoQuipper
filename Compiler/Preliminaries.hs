{- | This module implements a method used to simplify the original expression. In particular, the implmentation of the data constructors is explicitated, and
the are patterns are destructed, through the means of:

* the nth element of a tuple is accessed through the functions Access_1, Access_2, ..

* the label or tag of a record or data constructor is accessed using Label.

* the information contained in a record in accessed via Body_datacon.

The test of the case expressions are explicitated. Using a decision tree and chosen heuristics, a tree close to the optimal is produced.
This tree can then be used to generate the series of instructions needed to discriminate the patterns.

The patterns are also removed from the let expressions and the function arguments.
Note that the type constraints and location information are also removed.
-}

module Compiler.Preliminaries where

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
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- | Definition of a quantum data type.
data QType =
    QQubit
  | QUnit
  | QVar Variable
  | QTensor [QType]
  deriving (Eq, Show, Ord)

-- | The type of the associated circuits.
type CircType =
  (QType, QType)


-- | Convert a quantum data type written in the core syntax to 'Compiler.Preliminaries.Type'. 
convert_type :: C.Type -> QpState QType
convert_type (C.TBang _ C.TUnit) =
  return QUnit

convert_type (C.TBang _ (C.TVar a)) =
  return (QVar a)

convert_type (C.TBang _ C.TQubit) =
  return QQubit

convert_type (C.TBang _ (C.TTensor alist)) = do
  alist' <- List.foldr (\a rec -> do
        as <- rec
        a' <- convert_type a
        return $ a':as) (return []) alist
  return $ QTensor alist'

convert_type typ =
  throwQ $ ProgramError $ "The type " ++ pprint typ ++ " is not a quantum data type"
  

-- | Convert a quantum data type to a type.
convert_qtype :: QType -> C.Type
convert_qtype QUnit =
  C.TBang 0 C.TUnit
convert_qtype QQubit =
  C.TBang 0 C.TQubit
convert_qtype (QVar v) =
  C.TBang 0 $ C.TVar v
convert_qtype (QTensor qlist) =
  C.TBang 0 $ C.TTensor (List.map convert_qtype qlist)


-- | Return True iff the type contains no variables.
is_concrete :: QType -> Bool
is_concrete QQubit = True
is_concrete QUnit = True
is_concrete (QVar _) = False
is_concrete (QTensor qlist) =
  List.and $ List.map is_concrete qlist


-- | Convert the type of an unbox operator (only) to 'Compiler.Preliminaries.QType'.
-- An exception is raised if the given type is not of the form: @Circ (QType, QType) -> _@.
circuit_type :: C.Type -> QpState CircType
circuit_type (C.TBang _ (C.TArrow (C.TBang _ (C.TCirc t u)) _)) = do
  t' <- convert_type t
  u' <- convert_type u
  return (t', u')

circuit_type typ =
  throwQ $ ProgramError $ "The type " ++ pprint typ ++ " can't correspond to the type of unbox"


-- | Convert back a circuit type to the type of an unbox operator.
make_unbox_type :: CircType -> C.Type
make_unbox_type (t,u) =
  let t' = convert_qtype t
      u' = convert_qtype u in
  C.TBang 0 $ C.TArrow (C.TBang 0 $ C.TCirc t' u') (C.TBang 0 $ C.TArrow t' u')


-- | Return the types of all the occurences of \'unbox\' in the given expression.
unbox_types :: C.Expr -> QpState [CircType]
unbox_types (C.EFun _ _ e) =
  unbox_types e

unbox_types (C.EApp _ e f) = do
  ue <- unbox_types e
  uf <- unbox_types f
  return $ List.union ue uf

unbox_types (C.ETuple _ elist) =
  List.foldl (\rec e -> do
        us <- rec
        ue <- unbox_types e
        return $ List.union ue us) (return []) elist

unbox_types (C.ELet _ _ _ e f) = do
  ue <- unbox_types e
  uf <- unbox_types f
  return $ List.union ue uf

unbox_types (C.EIf _ e f g) = do
  ue <- unbox_types e
  uf <- unbox_types f
  ug <- unbox_types g
  return $ List.union ue $ List.union uf ug

unbox_types (C.EDatacon _ _ (Just e)) =
  unbox_types e

unbox_types (C.EMatch _ e blist) = do
  ue <- unbox_types e
  ulist <- List.foldl (\rec (_, e) -> do
        us <- rec
        ue <- unbox_types e
        return $ List.union ue us) (return []) blist
  return $ List.union ue ulist

unbox_types (C.EUnbox ref) = do
  ri <- ref_info ref
  case ri of
    Nothing ->
        throwQ $ ProgramError "Missing reference information"
    Just ri -> do
        a <- map_type $ C.r_type ri
        a' <- circuit_type a
        return [a']

unbox_types (C.EConstraint e _) =
  unbox_types e

unbox_types _ =
  return []


-- | Bind two types, producing a mapping from type variables to types.
bind_types :: C.Type -> C.Type -> QpState (IntMap QType)
bind_types (C.TBang _ (C.TVar v)) typ = do
  typ <- convert_type typ
  return $ IMap.singleton v typ
bind_types (C.TBang _ (C.TArrow t u)) (C.TBang _ (C.TArrow t' u')) = do
  bt <- bind_types t t'
  bu <- bind_types u u'
  return $ IMap.union bt bu
bind_types (C.TBang _ (C.TCirc t u)) (C.TBang _ (C.TCirc t' u')) = do
  bt <- bind_types t t'
  bu <- bind_types u u'
  return $ IMap.union bt bu
bind_types (C.TBang _ (C.TUser _ arg)) (C.TBang _ (C.TUser _ arg')) = do
  List.foldl (\rec (a, a') -> do
        map <- rec
        ba <- bind_types a a'
        return $ IMap.union ba map) (return IMap.empty) (List.zip arg arg')
bind_types (C.TBang _ (C.TTensor alist)) (C.TBang _ (C.TTensor alist')) =
  List.foldl (\rec (a, a') -> do
        map <- rec
        ba <- bind_types a a'
        return $ IMap.union ba map) (return IMap.empty) (List.zip alist alist')
bind_types _ _ =
  return IMap.empty


-- | Apply the binding produced by the function 'Compiler.Preliminaries.bind_types'.
app_bind :: IntMap QType -> QType -> QType
app_bind b (QVar v) =
  case IMap.lookup v b of
    Just t -> t
    Nothing -> QVar v
app_bind b (QTensor alist) =
  QTensor (List.map (app_bind b) alist)
app_bind _ t = t


-- | Return either the original unbox operator, if the type is concrete, or one of the argument
-- given in the list that has the appropriate type.
which_unbox :: CircType -> Map CircType Variable -> QpState (Either CircType Variable)
which_unbox a arg = do
  if is_concrete (fst a) && is_concrete (snd a) then
    return (Left a)
  else
    case Map.lookup a arg of
      Just x -> return (Right x)
      Nothing -> throwQ $ ProgramError $ "Undefined unbox operator: " ++ show a
 


-- | Modify an expression to disambiguate the use of the unbox operator: when the type can be inferred automically (in a non polymorphic context), then the operator is untouched,
-- else, the function using the unbox is modified to take the unbox operator as argument.
disambiguate_unbox_calls :: Map CircType Variable                     -- ^ The unbox operators available in the current context.
                         -> IntMap (C.Type, [CircType])               -- ^ Each modified function, along with its polymorphic type and the arguments it expects.
                         -> C.Expr                                    -- ^ The expresson to disambiguate.
                         -> QpState C.Expr                            -- ^ The disambiguated expression. 
disambiguate_unbox_calls arg _ (C.EUnbox ref) = do
  ri <- ref_info_err ref
  a <- map_type $ C.r_type ri
  a <- circuit_type a
  wu <- which_unbox a arg
  case wu of
    Left _ ->
        return (C.EUnbox ref)
    Right v ->
        return (C.EVar 0 v)
  
disambiguate_unbox_calls arg mod (C.EVar ref v) = do
  case IMap.lookup v mod of
    Nothing -> do
        return (C.EVar ref v)

    Just (typ, args) -> do
        -- If the type of the variable is concrete (no leftover type variables), then
        -- the unbox operators to apply can easily be derived.
        ri <- ref_info_err ref
        typ' <- map_type $ C.r_type ri
        b <- bind_types typ typ'
        let args' = List.map (\(a, a') -> (app_bind b a, app_bind b a')) args
        -- Use the function which_unbox to decide the arguments
        args' <- List.foldr (\a rec -> do
              as <- rec
              wua <- which_unbox a arg
              case wua of
                Left _ -> do
                    -- The type is concrete, create a reference to store it
                    ref <- create_ref
                    update_ref ref (\ri -> Just ri { C.r_type = make_unbox_type a })
                    return $ (C.EUnbox ref):as

                Right v ->
                    -- The type os not concrete, but a variable holding the right unbox implementation has been found
                    return $ (C.EVar 0 v):as) (return []) args'
        -- Finish by giving the unbox operators as arguments of the variable.
        List.foldl (\rec a -> do
              e <- rec
              return $ C.EApp 0 e a) (return $ C.EVar ref v) args'

disambiguate_unbox_calls arg mod (C.EGlobal ref v) = do
  case IMap.lookup v mod of
    Nothing -> do
        return (C.EGlobal ref v)

    Just (typ, args) -> do
        -- If the type of the variable is concrete (no leftover type variables), then
        -- the unbox operators to apply can easily be derived.
        ri <- ref_info_err ref
        typ' <- map_type $ C.r_type ri
        b <- bind_types typ typ'
        let args' = List.map (\(a, a') -> (app_bind b a, app_bind b a')) args
        -- Use the function which_unbox to decide the arguments
        args' <- List.foldr (\a rec -> do
              as <- rec
              wua <- which_unbox a arg
              case wua of
                Left _ -> do
                    -- The type is concrete, create a reference to store it
                    ref <- create_ref
                    update_ref ref (\ri -> Just ri { C.r_type = make_unbox_type a })
                    return $ (C.EUnbox ref):as

                Right v ->
                    -- The type os not concrete, but a variable holding the right unbox implementation has been found
                    return $ (C.EVar 0 v):as) (return []) args'
        -- Finish by giving the unbox operators as arguments of the variable.
        List.foldl (\rec a -> do
              e <- rec
              return $ C.EApp 0 e a) (return $ C.EGlobal ref v) args'


disambiguate_unbox_calls arg mod (C.ELet ref r (C.PVar ref' x) e f) = do
  -- Compute the list of non concrete unbox types used in the expression e
  need <- unbox_types e
  need <- return $ List.filter (\(a,a') -> not (is_concrete a && is_concrete a')) need
  
  -- Remove the types that can already be built using the existing arguments
  need <- return $ List.filter (\a -> not $ Map.member a arg) need

  -- Test whether the list is empty or not.
  case need of
    -- Nothing more to do
    [] -> do
        e' <- disambiguate_unbox_calls arg mod e
        f' <- disambiguate_unbox_calls arg mod f
        return (C.ELet ref r (C.PVar ref' x) e' f')

    -- Add new arguments to the variable x
    _ -> do    
        -- Retrieve the (polymorphic) type of the variable
        ref <- variable_reference x
        ri <- ref_info_err ref
        typ <- map_type $ C.r_type ri

        -- Add the variable and its (new) arguments to the mod context
        let mod' = IMap.insert x (typ, need) mod
        -- Add new argument variables to the arg context
        nargs <- List.foldr (\a rec -> do
              as <- rec
              v <- dummy_var
              return $ (a, v):as) (return []) need
        let arg' = Map.union (Map.fromList nargs) arg

        -- Convert the expression e using these new arguments
        e' <- disambiguate_unbox_calls arg' mod' e
        -- Convert the expression f (without the new arguments)
        f' <- disambiguate_unbox_calls arg mod' f

        -- Assemble the final expression
        let e'' = List.foldl (\e (_, v) ->
              C.EFun 0 (C.PVar 0 v) e) e' nargs
        return (C.ELet ref r (C.PVar ref' x) e'' f')

disambiguate_unbox_calls arg mod (C.ELet ref r p e f) = do
  need <- unbox_types e
  case need of
    -- In this case, no need to do anything
    [] -> do
        e' <- disambiguate_unbox_calls arg mod e
        f' <- disambiguate_unbox_calls arg mod f
        return (C.ELet ref r p e' f')

    -- In this case, since e must be a value, p and e must be of matching forms.
    -- Furthermore, only the expressions EDatacon and ETuple can contain a call to unbox.
    _ -> do
        case (p, e) of
          -- Tuple case : unfold the let-binding
          (C.PTuple _ plist, C.ETuple _ elist) -> do
              let elet = List.foldl (\f (p, e) ->
                    C.ELet ref r p e f) f (List.zip plist elist)
              disambiguate_unbox_calls arg mod elet

          -- Datacon case, again, unfold the let-binding
          (C.PDatacon _ dcon (Just p), C.EDatacon _ dcon' (Just e)) | dcon == dcon' -> do
              let elet = C.ELet ref r p e f
              disambiguate_unbox_calls arg mod elet
                                                                    | otherwise ->
              -- This case always leads to a matching error, so just replace it
              -- by the appropriate built-in function : PATTERN_ERROR
              return $ C.EBuiltin 0 "PATTERN_ERROR"

          -- All other cases should be unreachable
          _ ->
              throwQ $ ProgramError "disambiguate_unbox_calls: unexpected branching"


disambiguate_unbox_calls arg mod (C.EFun ref p e) = do
  e' <- disambiguate_unbox_calls arg mod e
  return (C.EFun ref p e')

disambiguate_unbox_calls arg mod (C.EApp ref e f) = do
  e' <- disambiguate_unbox_calls arg mod e
  f' <- disambiguate_unbox_calls arg mod f
  return (C.EApp ref e' f')

disambiguate_unbox_calls arg mod (C.EIf ref e f g) = do
  e' <- disambiguate_unbox_calls arg mod e
  f' <- disambiguate_unbox_calls arg mod f
  g' <- disambiguate_unbox_calls arg mod g
  return (C.EIf ref e' f' g')

disambiguate_unbox_calls arg mod (C.EDatacon ref dcon (Just e)) = do
  e' <- disambiguate_unbox_calls arg mod e
  return (C.EDatacon ref dcon (Just e'))

disambiguate_unbox_calls arg mod (C.EMatch ref e blist) = do
  e' <- disambiguate_unbox_calls arg mod e
  blist' <- List.foldr (\(p, e) rec -> do
        bs <- rec
        e' <- disambiguate_unbox_calls arg mod e
        return $ (p,e'):bs) (return []) blist
  return (C.EMatch ref e' blist')

disambiguate_unbox_calls arg mod (C.ETuple ref elist) = do
  elist' <- List.foldr (\e rec -> do
        es <- rec
        e' <- disambiguate_unbox_calls arg mod e
        return $ e':es) (return []) elist
  return (C.ETuple ref elist')

disambiguate_unbox_calls arg mod (C.EConstraint e _) =
  disambiguate_unbox_calls arg mod e

disambiguate_unbox_calls _ _ e =
  return e




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
  | EBox C.Type                                   -- ^ The constant @box[T]@.
  | EUnbox                                        -- ^ The constant @unbox@.
  | ERev                                          -- ^ The constant @rev@.

-- Unrelated
  | EBuiltin String                               -- ^ Built-in primitive: @#builtin s@.
  | EAccess Int Variable                          -- ^ Access the nth element of a tuple.
  | ELabel Variable                               -- ^ Return the label of an expression (supposedly a record).
  | EBody Datacon Variable                        -- ^ Return the body of a record that has a known label.
  deriving Show




-- | Representation of a decision tree, that decides which test to do first in order to minimize the number of comparisons.
data DecisionTree =
    Test TestLocation [(TestResult, DecisionTree)]           -- ^ Test the nth element of a tuple (a boolean). Depending on the result, different tests are taken.
  | Result Int                                               -- ^ The number of the matched pattern.
  deriving Show

-- | Ways of locating it self in a pattern.
-- The constructors indicate the action to take next.
data NextStep =
    InTuple Int        -- ^ The information is the Nth element of a tuple.
  | InDatacon Datacon  -- ^ The information is the argument of a record.
  | InLabel            -- ^ The information is the label of a record. Since at the moment of the test the label is unknown, this extractor is not annotated.
  deriving (Show, Eq, Ord)


-- | Position of the information relevant to a test in a pattern.
type TestLocation = [NextStep]


-- | The result of a test.
data TestResult =
    RInt Int                -- ^ The result of the test is an integer.
  | RRemainInt              -- ^ As a matching on integers is never complete, this constructor stands for all the integers not present in the test patterns.
  | RBool Bool              -- ^ The result is a boolean.
  | RDatacon Datacon        -- ^ The result is a data constructor.
  deriving (Show, Eq)

-- | Return the kind of a list of results. It is typically a result of the list.
rkind :: [TestResult] -> TestResult
rkind [] =
  error "rkind: empty list"
rkind (RInt _:_) = RInt 0
rkind (RRemainInt:_) = RInt 0
rkind (RBool _:_) = RBool True
rkind (RDatacon _:_) = RDatacon 0


-- | Build the list of the tests relevant to a pattern. The result of the test is returned each time.
relevant_tests :: C.Pattern -> QpState [(TestLocation, TestResult)]
relevant_tests p =
  -- The location in the pattern is passed as argument here (reversed though).
  let ptests = \ns p ->
        case p of
          C.PInt _ n -> return [(List.reverse ns, RInt n)]
          C.PBool _ b -> return [(List.reverse ns, RBool b)]
          C.PUnit _ -> return []
          C.PWildcard _ -> return []
          C.PVar _ _ -> return []
          C.PDatacon _ dcon Nothing -> do
              typ <- datacon_datatype dcon
              all <- all_data_constructors typ
              if List.length all == 1 then
                return []
              else
                return [(List.reverse $ InLabel:ns, RDatacon dcon)]
          C.PDatacon _ dcon (Just p) -> do
              typ <- datacon_datatype dcon
              all <- all_data_constructors typ
              if List.length all == 1 then
                ptests ((InDatacon dcon):ns) p
              else do
                tset <- ptests ((InDatacon dcon):ns) p
                return $ (List.reverse $ InLabel:ns, RDatacon dcon):tset
          C.PConstraint p _ -> ptests ns p
          C.PTuple _ plist ->
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
                                                  typ <- datacon_datatype dcon
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
                                                                                                    -- This case corresponds to the patterns var and wildcard, that match everything
                                                                                                    -- and yet are not relevant
                                                                                                    Nothing -> True) patterns
                                                             -- List of the tests relevant for these patterns
                                                             relevant_tests <- return $ List.filter (\(_, results) -> List.intersect (fst $ List.unzip results) patterns_ok /= []) rtests

                                                             -- If no test is relevant to the FIRST pattern, then it passes all the tests
                                                             case patterns_ok of
                                                               [] -> do
                                                                   -- A pattern error
                                                                   return $ (res, Result (-1)):subtrees

                                                               n:_ -> do
                                                                   -- Count the tests relevant to this particular pattern
                                                                   rtests <- return $ List.filter (\(_, results) -> List.elem n $ fst $ List.unzip results) relevant_tests
                                                                   if List.length rtests == 0 then
                                                                     -- No need to take other tests
                                                                     return $ (res, Result n):subtrees
                                                                   else do
                                                                     -- Else, do the normal stuff
                                                                     -- Build the subtree
                                                                     nsub <- build_tree relevant_tests patterns_ok
                                                                     -- Return the rest
                                                                     return $ (res, nsub):subtrees) (return []) results
                  
                                  -- Assemble the final tree
                                  return $ Test (fst $ next) subtrees in
                                build_tree)

  build_tree (Map.assocs tset) [0..(List.length plist)-1]


-- | Extract the variables of a pattern, and return the sequence of functions applications necessary to retrieve them.
pattern_variables :: C.Pattern -> [(TestLocation, Variable)]
pattern_variables p =
  let read_vars = \loc p ->
        case p of
          C.PVar _ x -> [(List.reverse loc, x)]
          C.PDatacon _ dcon (Just p) ->
              read_vars ((InDatacon dcon):loc) p
          C.PConstraint p _ -> read_vars loc p
          C.PTuple _ plist ->
              List.foldl (\vars (n, p) ->
                            let vars' = read_vars ((InTuple n):loc) p in
                            vars' ++ vars) [] (List.zip [0..(List.length plist) -1] plist)
          _ -> []
        in
  read_vars [] p


-- | Find variable closest to the infrmation one want to extract.
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
extract :: (TestLocation, Variable, TestLocation) -> QpState (Expr -> Expr, [(TestLocation, Variable)], Variable)
extract (prefix, var, loc) =
  case loc of
    -- The variable 'var' already contains what we want
    [] -> return ((\e -> e), [], var)
    -- Else 
    l:ls -> do
      -- Build some intermediary variables
      var' <- dummy_var
      let exp = case l of
                  InTuple n -> EAccess n var
                  InDatacon dcon -> EBody dcon var
                  InLabel -> ELabel var
      let nprefix = prefix ++ [l]
      (cont, updates, endvar) <- extract (nprefix, var', ls)
      return ((\e -> ELet Nonrecursive var' exp $ cont e), (nprefix, var'):updates, endvar)


-- | Same as extract, except that the variable holding the information is specified beforehand.
extract_var :: (TestLocation, Variable, TestLocation) -> Variable -> QpState (Expr -> Expr, [(TestLocation, Variable)])
extract_var (prefix, var, loc) endvar =
  case loc of
    -- The variable 'var' already contains what we want
    [] -> return ((\e -> ELet Nonrecursive endvar (EVar var) e), [])
    -- The LAST action is a tuple accessor
    [InTuple n] -> return ((\e -> ELet Nonrecursive endvar (EAccess n var) e), [])
    -- The LAST action is a destructor
    [InDatacon dcon] -> return ((\e -> ELet Nonrecursive endvar (EBody dcon var) e), [])
    -- Else use an intermediary variable
    l:ls -> do
        var' <- dummy_var
        let exp = case l of
                    InTuple n -> EAccess n var
                    InDatacon dcon -> EBody dcon var
                    InLabel -> ELabel var
        nprefix <- return $ prefix ++ [l]
        (cont, updates) <- extract_var (nprefix, var', ls) endvar
        return ((\e -> ELet Nonrecursive var' exp $ cont e), (nprefix, var'):updates)


-- | Using a decision tree, explain the tests that have to be done to compute a pattern matching.
simplify_pattern_matching :: C.Expr -> [(C.Pattern, C.Expr)] -> QpState Expr
simplify_pattern_matching e blist = do
  patterns <- return $ fst $ List.unzip blist
  e' <- remove_patterns_in_expr e
  dtree <- build_decision_tree patterns                         

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
                                  teste <- case rkind (fst $ List.unzip results) of
                                             RInt _ -> do 
                                                 -- Isolate the infinite case, and put it at the end of the list
                                                 ([(_, remains)], others) <- return $ List.partition (\(r, _) -> case r of
                                                                                                  RRemainInt -> True
                                                                                                  _ -> False) results
                                                 lastcase <- unbuild remains extracted
                                                 -- Eliminate the cases with the same results as the infinite case (= Result -1)
                                                 others <- return $ List.filter (\(res, subtree) ->
                                                                                   case subtree of
                                                                                     Result (-1) -> False
                                                                                     _ -> True) others

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
                                                                         cases <- rec
                                                                         dcon <- return $ case rdcon of {RDatacon dcon -> dcon; _ -> -1}
                                                                         e <- unbuild subtree extracted
                                                                         return $ (dcon, e):cases) (return []) results
                                                 return $ EMatch (EVar var') cases

                                             RRemainInt ->
                                                 throwQ $ ProgramError "Unexpected result 'RRemainInt'"

                                  -- Complete the sequence with the variable extraction
                                  return $ initseq teste
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
remove_patterns_in_expr (C.EVar _ x) =
  return $ EVar x

remove_patterns_in_expr (C.EGlobal _ x) =
  return $ EGlobal x

remove_patterns_in_expr (C.EFun _ p e) = do
   -- Check whether the expression is already  or not
  case p of
    -- The pattern is only one variable: do nothing
    C.PVar _ x -> do
      e' <- remove_patterns_in_expr e
      return $ EFun x e'

    -- If the pattern is more complicated, replace it by a variable
    _ -> do
      x <- dummy_var
      e' <- remove_patterns_in_expr $ C.ELet 0 Nonrecursive p (C.EVar 0 x) e
      return $ EFun x e'

remove_patterns_in_expr (C.EApp _ e f) = do
  e' <- remove_patterns_in_expr e
  f' <- remove_patterns_in_expr f
  return $ EApp e' f'

remove_patterns_in_expr (C.EUnit _) = do
  return EUnit

remove_patterns_in_expr (C.ETuple _ elist) = do
  elist' <- List.foldl (\rec e -> do
                          es <- rec
                          e' <- remove_patterns_in_expr e
                          return $ e':es) (return []) elist
  return $ ETuple $ List.reverse elist'

remove_patterns_in_expr (C.ELet _ r p e f) = do
  e' <- remove_patterns_in_expr e
  case p of
    -- If the pattern is unit
    (C.PUnit _) -> do
        f' <- remove_patterns_in_expr f
        return $ ESeq e' f'

    -- If the pattern is boolean
    (C.PBool _ b) -> do
        f' <- remove_patterns_in_expr f
        return $ if b then
                   EIf e' f' (EBuiltin "PATTERN_ERROR")
                 else 
                   EIf e' (EBuiltin "PATTERN_ERROR") f'

    -- If the pattern is an integer: do nothing
    (C.PInt _ n) -> do
        f' <- remove_patterns_in_expr f
        x <- dummy_var
        return $ ELet r x f' (
                   EIf (EApp (EApp (EBuiltin "EQ") (EInt n)) (EVar x)) f' (EBuiltin "PATTERN_ERROR"))

    -- If the pattern is one variable, do nothing
    -- The let binding can't be removed because of let-polymorphism
    C.PVar _ x -> do
        f' <- remove_patterns_in_expr f
        return $ ELet r x e' f'

    -- If the pattern is a pair of variables, this is the case of tensor elimination
    C.PTuple _ plist -> do
        -- The tuple will be saved in that variable
        xp <- dummy_var
        -- For each element of the tuple, the variable is extracted using #1 #2 ..
        (_,f) <- List.foldl (\rec p -> do
                               (n, e) <- rec
                               return (n+1, C.ELet 0 r p (C.EApp 0 (C.EBuiltin 0 $ "#" ++ show n) (C.EVar 0 xp)) e)) (return (0, f)) plist
        e' <- remove_patterns_in_expr e
        f' <- remove_patterns_in_expr f
        return $ ELet r xp e' f'

    -- If the pattern is a datacon, remove_patterns_in_expr by adding a pattern matching
    C.PDatacon _ dcon Nothing -> do
        f' <- remove_patterns_in_expr f
        return $ EMatch e' [(dcon, f')]

    C.PDatacon _ dcon (Just p) -> do
        x <- dummy_var
        ep <- remove_patterns_in_expr (C.ELet 0 Nonrecursive p (C.EApp 0 (C.EBuiltin 0 "EXTRACT") (C.EVar 0 x)) f)
        return $ ELet Nonrecursive x e' (
                   EMatch (EVar x) [(dcon, ep)]
                 )
    -- The wildcard
    C.PWildcard _ -> do
        f' <- remove_patterns_in_expr f
        return $ ESeq e' f'

    -- Others
    C.PConstraint _ _ ->
        throwQ $ ProgramError "Constraint remaining in pattern"


remove_patterns_in_expr (C.EBool _ b) = do
  return $ EBool b

remove_patterns_in_expr (C.EInt _ n) = do
  return $ EInt n

remove_patterns_in_expr (C.EIf _ e f g) = do
  e' <- remove_patterns_in_expr e
  f' <- remove_patterns_in_expr f
  g' <- remove_patterns_in_expr g
  return $ EIf e' f' g'

remove_patterns_in_expr (C.EDatacon _ dcon Nothing) = do
  return $ EDatacon dcon Nothing

remove_patterns_in_expr (C.EDatacon _ dcon (Just e)) = do
  e' <- remove_patterns_in_expr e
  return $ EDatacon dcon $ Just e'

remove_patterns_in_expr (C.EMatch _ e blist) = do
  simplify_pattern_matching e blist

remove_patterns_in_expr (C.EBox _ typ) = do
  return $ EBox typ

remove_patterns_in_expr (C.EUnbox _) = do
  return EUnbox

remove_patterns_in_expr (C.ERev _) = do
  return ERev

remove_patterns_in_expr (C.EBuiltin _ s) =
  return (EBuiltin s)
  
remove_patterns_in_expr (C.EConstraint e t) =
  remove_patterns_in_expr e




-- * Printing functions.

-- | Pretty-print an expression using Hughes's and Peyton Jones's
-- pretty printer combinators. The type 'Doc' is defined in the library
-- "Text.PrettyPrint.HughesPJ" and allows for nested documents.
print_doc :: Lvl                   -- ^ Maximum depth.
          -> Expr                  -- ^ Expression to print.
          -> (Variable -> String)  -- ^ Rendering of term variables.
          -> (Variable -> String)  -- ^ Rendering of data constructors.
          -> Doc                   -- ^ Resulting PP document.
print_doc _ (EAccess n v) fvar _ =
  text ("#" ++ show n) <+> text (fvar v)

print_doc _ (ELabel v) fvar _ =
  text "LABEL" <+> text (fvar v)

print_doc _ (EBody dcon v) fvar _ =
  text ("EXTRACT_" ++ show dcon) <+> text (fvar v)

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
  text s

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
                        let pmatch = char '|' <+> text (show p) <+> text "->" <+> print_doc dlv f fvar fdata in
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
  sprintn lv e = genprint lv e [subvar '%', subvar 'D']
  sprint e = sprintn defaultLvl e
  pprint e = sprintn Inf e


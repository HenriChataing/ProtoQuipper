{- | This module implements a method used to simplify the original expression. In particular, the implementation of the data constructors is made explicit, and
the patterns are destructed, through the means of:

* the /n/th element of a tuple is accessed through the functions Access_1, Access_2, ..

* the label or tag of a record or data constructor is accessed using Label.

* the information contained in a record in accessed via Body_datacon.

The tests of the case expressions are make explicit. Using a decision tree and chosen heuristics, a tree close to the optimal is produced.
This tree can then be used to generate the series of instructions needed to discriminate the patterns.

The patterns are also removed from the let expressions and the function arguments.
Note that the type constraints and location information are also removed.
-}

module Compiler.Preliminaries where

import Classes
import Utils

import Parsing.Location (extent_unknown)

--import Monad.QpState
import Monad.Error

import qualified Core.Syntax as C

import Compiler.SimplSyntax
import Compiler.Circ

import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap


-- | Update the tag access function of a type.
set_tagaccess :: Algebraic -> (Variable -> Expr) -> QpState ()
set_tagaccess id gettag = do
  ctx <- get_context
  set_context ctx { tagaccess = IMap.insert id gettag $ tagaccess ctx }


-- | Return the tag accessor of an algebraic type. If the tag access is undefined,
-- then the function \choose_implementation\ is called to implement it.
get_tagaccess :: Algebraic -> QpState (Variable -> Expr)
get_tagaccess id = do
  ctx <- get_context
  case IMap.lookup id $ tagaccess ctx of
    Just gettag -> return gettag
    Nothing -> fail "Preliminaries:get_tagaccess: undefined accessor"



-- | Settle the implementation (machine representation) of all the constructors of an algebraic type.
choose_implementation :: Algebraic -> QpState ()
choose_implementation id = do
  alg <- algebraic_def id
  let (_, datas) = C.definition alg
  case datas of
    -- Cases with one constructor:
    -- The tag is omitted. No definition of the function gettag is needed.
    [(dcon, Just _)] -> do
        update_datacon dcon (\ddef -> Just ddef { C.construct = Right (\e -> e), C.deconstruct = \v -> EVar v })

    [(dcon, Nothing)] ->
        update_datacon dcon (\def -> Just def { C.construct = Left $ EInt 0, C.deconstruct = \v -> EInt 0 })

    -- Cases with several constrcutors
    _ -> do
        -- First thing : count the constructors taking an argument.
        let (with_args, no_args) = List.partition ((/= Nothing) . snd) datas

        List.foldl (\rec (dcon, _) -> do
              rec
              update_datacon dcon (\ddef -> Just ddef { C.construct = Right (\e -> ETuple [EInt (C.tag ddef),e]), C.deconstruct = \v -> EAccess 1 v })
            ) (return ()) with_args
        -- The constructors with no argument are represented by just their tag. The deconstruct function is not needed.
        List.foldl (\rec (dcon, _) -> do
              rec
              update_datacon dcon (\ddef -> Just ddef { C.construct = Left $ ETuple [EInt (C.tag ddef)] })
            ) (return ()) no_args
        -- The tag is the first element of the tuple.
        set_tagaccess id $ \v -> EAccess 0 v




-- | Convert a quantum data type written in the core syntax to 'Compiler.Preliminaries.Type'.
convert_type :: C.Type -> QpState QType
convert_type (C.TypeAnnot _ C.TUnit) =
  return QUnit

convert_type (C.TypeAnnot _ (C.TypeVar a)) =
  return (QVar a)

convert_type (C.TypeAnnot _ C.TQubit) =
  return QQubit

convert_type (C.TypeAnnot _ (C.TTensor alist)) = do
  alist' <- List.foldr (\a rec -> do
        as <- rec
        a' <- convert_type a
        return $ a':as) (return []) alist
  return $ QTensor alist'

convert_type typ =
  fail $ "Preliminaries:convert_type: illegal argument: " ++ pprint typ


-- | Convert a quantum data type to a type.
convert_qtype :: QType -> C.Type
convert_qtype QUnit =
  C.TypeAnnot 0 C.TUnit
convert_qtype QQubit =
  C.TypeAnnot 0 C.TQubit
convert_qtype (QVar v) =
  C.TypeAnnot 0 $ C.TypeVar v
convert_qtype (QTensor qlist) =
  C.TypeAnnot 0 $ C.TTensor (List.map convert_qtype qlist)


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
circuit_type (C.TypeAnnot _ (C.TArrow (C.TypeAnnot _ (C.TCirc t u)) _)) = do
  t' <- convert_type t
  u' <- convert_type u
  return (t', u')

circuit_type typ =
  fail $ "Preliminaries:circuit_type: illegal argument: " ++ show typ


-- | Convert back a circuit type to the type of an unbox operator.
make_unbox_type :: CircType -> C.Type
make_unbox_type (t,u) =
  let t' = convert_qtype t
      u' = convert_qtype u in
  C.TypeAnnot 0 $ C.TArrow (C.TypeAnnot 0 $ C.TCirc t' u') (C.TypeAnnot 0 $ C.TArrow t' u')


-- | Return the types of all the occurences of \'unbox\' in the given expression.
unbox_types :: C.Expr -> QpState [C.Type]
unbox_types (C.EFun _ _ e) =
  unbox_types e

unbox_types (C.EApp e f) = do
  ue <- unbox_types e
  uf <- unbox_types f
  return $ List.unionBy C.eq_skel ue uf

unbox_types (C.ETuple _ elist) =
  List.foldl (\rec e -> do
        us <- rec
        ue <- unbox_types e
        return $ List.unionBy C.eq_skel ue us) (return []) elist

unbox_types (C.ELet _ _ e f) = do
  ue <- unbox_types e
  uf <- unbox_types f
  return $ List.union ue uf

unbox_types (C.EIf e f g) = do
  ue <- unbox_types e
  uf <- unbox_types f
  ug <- unbox_types g
  return $ List.unionBy C.eq_skel ue $ List.union uf ug

unbox_types (C.EDatacon _ _ (Just e)) =
  unbox_types e

unbox_types (C.EMatch e blist) = do
  ue <- unbox_types e
  ulist <- List.foldl (\rec (_, e) -> do
        us <- rec
        ue <- unbox_types e
        return $ List.unionBy C.eq_skel ue us) (return []) blist
  return $ List.union ue ulist

unbox_types (C.EUnbox ref) = do
  ri <- ref_info ref
  case ri of
    Nothing ->
        fail $ "Preliminaries:unbox_types: undefined reference: " ++ show ref
    Just ri -> do
        a <- map_type $ C.rtype ri
        return [a]

unbox_types (C.EConstraint e _) =
  unbox_types e

unbox_types _ =
  return []


-- | Bind two types, producing a mapping from type variables to types.
bind_types :: C.Type -> C.Type -> QpState (IntMap C.Type)
bind_types (C.TypeAnnot _ (C.TypeVar v)) typ = do
  return $ IMap.singleton v typ
bind_types (C.TypeAnnot _ (C.TArrow t u)) (C.TypeAnnot _ (C.TArrow t' u')) = do
  bt <- bind_types t t'
  bu <- bind_types u u'
  return $ IMap.union bt bu
bind_types (C.TypeAnnot _ (C.TCirc t u)) (C.TypeAnnot _ (C.TCirc t' u')) = do
  bt <- bind_types t t'
  bu <- bind_types u u'
  return $ IMap.union bt bu
bind_types (C.TypeAnnot _ (C.TAlgebraic _ arg)) (C.TypeAnnot _ (C.TAlgebraic _ arg')) = do
  List.foldl (\rec (a, a') -> do
        map <- rec
        ba <- bind_types a a'
        return $ IMap.union ba map) (return IMap.empty) (List.zip arg arg')
bind_types (C.TypeAnnot _ (C.TTensor alist)) (C.TypeAnnot _ (C.TTensor alist')) =
  List.foldl (\rec (a, a') -> do
        map <- rec
        ba <- bind_types a a'
        return $ IMap.union ba map) (return IMap.empty) (List.zip alist alist')
bind_types _ _ =
  return IMap.empty


-- | Apply the binding produced by the function 'Compiler.Preliminaries.bind_types'.
app_bind :: IntMap C.Type -> C.Type -> C.Type
app_bind b (C.TypeAnnot n (C.TypeVar v)) =
  case IMap.lookup v b of
    Just t -> t
    Nothing -> C.TypeAnnot n $ C.TypeVar v
app_bind b (C.TypeAnnot n (C.TTensor alist)) =
  C.TypeAnnot n $ C.TTensor (List.map (app_bind b) alist)
app_bind b (C.TypeAnnot n (C.TArrow t u)) =
  C.TypeAnnot n $ C.TArrow (app_bind b t) (app_bind b u)
app_bind b (C.TypeAnnot n (C.TCirc t u)) =
  C.TypeAnnot n $ C.TCirc (app_bind b t) (app_bind b u)
app_bind _ t = t


-- | Return either the original unbox operator, if the type is concrete, or one of the argument
-- given in the list that has the appropriate type.
which_unbox :: C.Type -> [(C.Type, Variable)] -> QpState (Either C.Type Variable)
which_unbox a arg =
  case List.find (\(t, x) -> C.eq_skel a t) arg of
    Just (_, x) -> return (Right x)
    Nothing -> return (Left a)


-- | Modify an expression to disambiguate the use of the unbox operator: when the type can be inferred automically (in a non polymorphic context), then the operator is untouched,
-- else, the function using the unbox is modified to take the unbox operator as argument.
disambiguate_unbox_calls :: [(C.Type, Variable)]                      -- ^ The unbox operators available in the current context.
                         -> IntMap (C.Type, [C.Type])                 -- ^ Each modified (local) function, along with its polymorphic type and the arguments it expects.
                         -> C.Expr                                    -- ^ The expression to disambiguate.
                         -> QpState C.Expr                            -- ^ The disambiguated expression.
disambiguate_unbox_calls arg _ (C.EUnbox ref) = do
  ri <- ref_info_err ref
  a <- map_type $ C.rtype ri
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
        typ' <- map_type $ C.rtype ri
        b <- bind_types typ typ'
        let args' = List.map (app_bind b) args
        -- Use the function which_unbox to decide the arguments
        args' <- List.foldr (\a rec -> do
              as <- rec
              wua <- which_unbox a arg
              case wua of
                Left _ -> do
                    -- The type is concrete, create a reference to store it
                    update_ref ref (\ri -> Just ri { C.rtype = a })
                    return $ (C.EUnbox ref):as

                Right v ->
                    -- The type os not concrete, but a variable holding the right unbox implementation has been found
                    return $ (C.EVar 0 v):as) (return []) args'
        -- Finish by giving the unbox operators as arguments of the variable.
        List.foldl (\rec a -> do
              e <- rec
              return $ C.EApp e a) (return $ C.EVar ref v) args'

disambiguate_unbox_calls arg mod (C.EGlobal ref v) = do
  cc <- call_convention v
  case cc of
    Nothing -> do
        return (C.EGlobal ref v)

    Just args -> do
        t <- global_type v
        let typ = C.type_of_typescheme t
        -- If the type of the variable is concrete (no leftover type variables), then
        -- the unbox operators to apply can easily be derived.
        ri <- ref_info_err ref
        typ' <- map_type $ C.rtype ri
        b <- bind_types typ typ'
        let args' = List.map (app_bind b) args
        -- Use the function which_unbox to decide the arguments
        args' <- List.foldr (\a rec -> do
              as <- rec
              wua <- which_unbox a arg
              case wua of
                Left _ -> do
                    -- The type is concrete, create a reference to store it
                    ref <- create_ref
                    update_ref ref (\ri -> Just ri { C.rtype = a })
                    return $ (C.EUnbox ref):as

                Right v ->
                    -- The type os not concrete, but a variable holding the right unbox implementation has been found
                    return $ (C.EVar 0 v):as) (return []) args'
        -- Finish by giving the unbox operators as arguments of the variable.
        List.foldl (\rec a -> do
              e <- rec
              return $ C.EApp e a) (return $ C.EGlobal ref v) args'


disambiguate_unbox_calls arg mod (C.ELet r p e f) = do
  -- First disambiguate the calls from e
  e' <- disambiguate_unbox_calls arg mod e

  -- Then pick up the remaining unbox calls
  need <- unbox_types e'
  need <- return $ List.filter (\a -> not $ C.is_concrete a) need

  -- Remove the types that can already be built using the existing arguments
  need <- return $ List.filter (\a -> List.find (\(b, _) -> C.eq_skel a b) arg == Nothing) need

  -- Test whether the list is empty or not.
  case need of
    -- Nothing more to do
    [] -> do
        f' <- disambiguate_unbox_calls arg mod f
        return (C.ELet r p e' f')

    -- Add new arguments to the variable x
    _ -> do
        case (p, e') of
          (C.PWildcard ref', _) -> do
              -- Add new argument variables to the arg context
              nargs <- List.foldr (\a rec -> do
                    as <- rec
                    v <- create_var "u"
                    return $ (a, v):as) (return []) need
              let arg' = nargs ++ arg

              -- Convert the expression e using these new arguments
              e' <- disambiguate_unbox_calls arg' mod e'
              -- Convert the expression f (without the new arguments)
              f' <- disambiguate_unbox_calls arg mod f

              -- Assemble the final expression
              let e'' = List.foldl (\e (_, v) ->
                    C.EFun 0 (C.PVar 0 v) e) e' nargs
              return (C.ELet r (C.PWildcard ref') e'' f')


          (C.PVar ref' x, _) -> do
              -- Retrieve the (polymorphic) type of the variable
              ri <- ref_info_err ref'
              typ <- map_type $ C.rtype ri

              -- Check whether the variable is global or not
              g <- is_global x
              if g then do
                -- Specify the calling convention for x
                set_call_convention x need
              else
                -- Do nothing
                return ()

              -- Add the variable and its (new) arguments to the mod context
              let mod' = IMap.insert x (typ, need) mod

              -- Add new argument variables to the arg context
              nargs <- List.foldr (\a rec -> do
                    as <- rec
                    v <- create_var "u"
                    return $ (a, v):as) (return []) need
              let arg' = nargs ++ arg

              -- Convert the expression e using these new arguments
              e' <- disambiguate_unbox_calls arg' mod' e'
              -- Convert the expression f (without the new arguments)
              f' <- disambiguate_unbox_calls arg mod' f

              -- Assemble the final expression
              let e'' = List.foldl (\e (_, v) ->
                    C.EFun 0 (C.PVar 0 v) e) e' nargs
              return (C.ELet r (C.PVar ref' x) e'' f')


          (C.PTuple _ plist, C.ETuple _ elist) -> do
              let elet = List.foldl (\f (p, e) ->
                    C.ELet r p e f) f (List.zip plist elist)
              disambiguate_unbox_calls arg mod elet

          -- Datacon case, again, unfold the let-binding
          (C.PDatacon _ dcon (Just p), C.EDatacon ref' dcon' (Just e)) | dcon == dcon' -> do
              let elet = C.ELet r p e' f
              disambiguate_unbox_calls arg mod elet
                                                                       | otherwise -> do
              -- This case always leads to a matching error.
              -- Raise a warning
              ri <- ref_info_err ref'
              warnQ FailedMatch (C.extent ri)
              return $ C.EError (show (C.extent ri) ++ ":pattern error")

          -- All other cases should be unreachable
          (p, _) ->
              fail $ "Preliminaries:disambiguate_unbox_calls: unexpected pattern: " ++ pprint p


disambiguate_unbox_calls arg mod (C.EFun ref p e) = do
  e' <- disambiguate_unbox_calls arg mod e
  return (C.EFun ref p e')

disambiguate_unbox_calls arg mod (C.EApp e f) = do
  e' <- disambiguate_unbox_calls arg mod e
  f' <- disambiguate_unbox_calls arg mod f
  return (C.EApp e' f')

disambiguate_unbox_calls arg mod (C.EIf e f g) = do
  e' <- disambiguate_unbox_calls arg mod e
  f' <- disambiguate_unbox_calls arg mod f
  g' <- disambiguate_unbox_calls arg mod g
  return (C.EIf e' f' g')

disambiguate_unbox_calls arg mod (C.EDatacon ref dcon (Just e)) = do
  e' <- disambiguate_unbox_calls arg mod e
  return (C.EDatacon ref dcon (Just e'))

disambiguate_unbox_calls arg mod (C.EMatch e blist) = do
  e' <- disambiguate_unbox_calls arg mod e
  blist' <- List.foldr (\(p, e) rec -> do
        bs <- rec
        e' <- disambiguate_unbox_calls arg mod e
        return $ (p,e'):bs) (return []) blist
  return (C.EMatch e' blist')

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
  | InTag Algebraic    -- ^ The information is the label of a record. The label is specific to a type.
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


-- | Return the kind of a list of results. It is typically a result of the list.
rkind :: [TestResult] -> TestResult
rkind [] =
  throwNE $ ProgramError "Preliminaries:rkind: empty list"
rkind (RInt _:_) = RInt 0
rkind (ROtherInt _:_) = RInt 0
rkind (RBool _:_) = RBool True
rkind (RDatacon _:_) = RDatacon 0
rkind (ROtherDatacon _:_) = RDatacon 0


-- | On the supposion that the result is 'RInt', return the associated integer.
int_of_result :: TestResult -> Int
int_of_result (RInt i) = i
int_of_result _ = 0

-- | On the supposition that the result is 'RDatacon', return the associated constructor.
datacon_of_result :: TestResult -> Datacon
datacon_of_result (RDatacon d) = d
datacon_of_result _ = 0


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
                return [(List.reverse $ (InTag typ):ns, RDatacon dcon)]
          C.PDatacon _ dcon (Just p) -> do
              typ <- datacon_datatype dcon
              all <- all_data_constructors typ
              if List.length all == 1 then
                ptests ((InDatacon dcon):ns) p
              else do
                tset <- ptests ((InDatacon dcon):ns) p
                return $ (List.reverse $ (InTag typ):ns, RDatacon dcon):tset
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
                       return $ (ROtherInt $ List.map int_of_result results):results
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
                    let relevant_tests = List.filter (\(_, results) -> List.intersect (fst $ List.unzip results) patterns_ok /= []) rtests
                        relevant_tests' = List.map (\(t, results) -> (t, List.filter (\(p, _) -> List.elem p patterns_ok) results)) relevant_tests

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
                          rtests <- return $ List.filter (\(_, results) -> List.elem n $ fst $ List.unzip results) relevant_tests'
                          if List.length rtests == 0 then
                            -- No need to take other tests
                            return ((res, Result n):subtrees, unmatched)
                          else do
                            -- Else, do the normal stuff
                            -- Build the subtree
                            (nsub, unmatched') <- build_tree relevant_tests' patterns_ok
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
      modify_pattern _ [] (RInt n) = C.PInt 0 n
      modify_pattern _ [] (RBool b) = C.PBool 0 b
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
        throwNE $ ProgramError "Preliminaries:modify_pattern: illegal arguments"


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
extract :: (TestLocation, Variable, TestLocation) -> QpState (Expr -> Expr, [(TestLocation, Variable)], Variable)
extract (prefix, var, loc) =
  case loc of
    -- The variable 'var' already contains what we want
    [] -> return ((\e -> e), [], var)
    -- Else
    l:ls -> do
      -- Build some intermediary variables
      var' <- create_var "x"
      exp <- case l of
            InTuple n ->
                return $ EAccess n var
            InDatacon dcon -> do
                deconstruct <- datacon_def dcon >>= return . C.deconstruct
                return $ deconstruct var
            InTag typ -> do
                gettag <- get_tagaccess typ
                return $ gettag var

      let nprefix = prefix ++ [l]
      (cont, updates, endvar) <- extract (nprefix, var', ls)
      return ((\e -> ELet var' exp $ cont e), (nprefix, var'):updates, endvar)


-- | Same as extract, except that the variable holding the information is specified beforehand.
extract_var :: (TestLocation, Variable, TestLocation) -> Variable -> QpState (Expr -> Expr, [(TestLocation, Variable)])
extract_var (prefix, var, loc) endvar =
  case loc of
    -- The variable 'var' already contains what we want
    [] -> return ((\e -> ELet endvar (EVar var) e), [])
    -- The LAST action is a tuple accessor
    [InTuple n] -> return ((\e -> ELet endvar (EAccess n var) e), [])
    -- The LAST action is a destructor
    [InDatacon dcon] -> do
        deconstruct <- datacon_def dcon >>= return . C.deconstruct
        return ((\e -> ELet endvar (deconstruct var) e), [])

    -- Else use an intermediary variable
    l:ls -> do
        var' <- create_var "x"
        exp <- case l of
            InTuple n ->
                return $ EAccess n var
            InDatacon dcon -> do
                deconstruct <- datacon_def dcon >>= return . C.deconstruct
                return $ deconstruct var
            InTag typ -> do
                gettag <- get_tagaccess typ
                return $ gettag var

        nprefix <- return $ prefix ++ [l]
        (cont, updates) <- extract_var (nprefix, var', ls) endvar
        return ((\e -> ELet var' exp $ cont e), (nprefix, var'):updates)


-- | Using a decision tree, explain the tests that have to be done to compute a pattern matching.
simplify_pattern_matching :: C.Expr -> [(C.Pattern, C.Expr)] -> QpState Expr
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
              teste <- case rkind (fst $ List.unzip results) of
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
                              Nothing -> fail "Preliminaries:simplify_pattern_matching: missing case True"
                        rfalse <- case List.lookup (RBool False) results of
                              Just t -> return t
                              Nothing -> fail "Preliminaries:simplify_pattern_matching: missing case False"
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
                                    RDatacon dcon -> datacon_def dcon >>= return . C.tag
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
                        fail "Preliminaries:simplify_pattern_matching: unexpected result 'ROtherInt'"
                    ROtherDatacon _ ->
                        fail "Preliminaries:simplify_pattern_matching: unexpected result 'ROtherDatacon'"

              -- Complete the sequence with the variable extraction
              return $ initseq teste

  -- If the test expression is not a variable, then push it in a variable
  case e' of
    EVar iniTypeVar -> do
        unbuild dtree [([], iniTypeVar)]
    _ -> do
        iniTypeVar <- create_var "x"
        tests <- unbuild dtree [([], iniTypeVar)]
        return $ ELet iniTypeVar e' tests



-- | Remove the patterns. Some are left in the match expressions, but should only be of the form @A _@ or @_@, where @_@ is the wildcard.
remove_patterns :: C.Expr -> QpState Expr
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
      x <- create_var "x"
      return $ EFun x e'

    -- If the pattern is more complicated, replace it by a variable
    _ -> do
      x <- create_var "x"
      e' <- remove_patterns $ C.ELet Nonrecursive p (C.EVar 0 x) e
      return $ EFun x e'

remove_patterns (C.EApp e f) = do
  e' <- remove_patterns e
  f' <- remove_patterns f
  return $ EApp e' f'

remove_patterns (C.EUnit _) = do
  return EUnit

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
        fail "Preliminaries:remove_patterns: unexpected recursive object"

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
  fail "Preliminaries:remove_patterns: unexpected recursive binding"

remove_patterns (C.EBool _ b) = do
  return $ EBool b

remove_patterns (C.EInt _ n) = do
  return $ EInt n

remove_patterns (C.EIf e f g) = do
  e' <- remove_patterns e
  f' <- remove_patterns f
  g' <- remove_patterns g
  return $ EMatch e' [(1,f')] g'

remove_patterns (C.EDatacon _ dcon Nothing) = do
  ddef <- datacon_def dcon
  -- If the data constructor expected an argument, then return a pointer to an implementation
  -- of the incomplete constructor.
  if C.implementation ddef == -1 then do
    Left construct <- datacon_def dcon >>= return . C.construct
    return construct
  else
    return $ EGlobal $ C.implementation ddef

remove_patterns (C.EDatacon _ dcon (Just e)) = do
  Right construct <- datacon_def dcon >>= return . C.construct
  e' <- remove_patterns e
  return $ construct e'

remove_patterns (C.EMatch e blist) = do
  simplify_pattern_matching e blist

remove_patterns (C.EBox _ typ) = do
  typ <- convert_type typ
  x <- request_box typ
  return (EVar x)

remove_patterns (C.EUnbox ref) = do
  ri <- ref_info_err ref
  let typ = C.rtype ri
  typ <- map_type typ
  (t, u) <- circuit_type typ
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

remove_patterns (C.EConstraint e t) =
  remove_patterns e

remove_patterns (C.EError msg) =
  return (EError msg)


-- | Modify the body of a module by applying the function 'disambiguate_unbox_calls' and 'remove_pattern'
-- to all the top-level declarations.
transform_declarations :: [C.Declaration] -> QpState [Declaration]
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
              need <- return $ List.filter (\a -> not $ C.is_concrete a) need

              -- Unresolved unbox operators
              if need /= [] then do
                typ <- global_type x >>= return . C.type_of_typescheme

                -- Specify the calling convention for x
                set_call_convention x need

                -- Add the variable and its (new) arguments to the mod context
                let mod' = IMap.insert x (typ, need) mod

                -- Add new argument variables to the arg context
                args <- List.foldr (\a rec -> do
                      as <- rec
                      v <- create_var "u"
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
                      typ <- global_type x >>= return . C.type_of_typescheme
                      if C.is_fun typ then do
                        -- Necessary eta-expansion.
                        a <- create_var "x"
                        return ((DLet External x $ EFun a (EApp e' $ EVar a)):decls, mod)
                      else
                        return ((DLet External x e'):decls, mod)

      ) (return ([], IMap.empty)) decls

  -- Retrieve the declaration of quantum operations
  qops <- clear_circuit_ops

  return $ qops ++ List.reverse decls



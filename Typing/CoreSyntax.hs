{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}


-- | This module defines the /internal syntax/ of Proto-Quipper.
-- Compared to the /surface syntax/ defined in "Parsing.Syntax", the
-- grammar of types has been considerably modified to facilitate type
-- inference. For greater efficiency, all term and type variables are
-- labelled by a unique id, which serves as a lookup key in maps and
-- other data structures.
module Typing.CoreSyntax where

import Classes
import Utils

import Parsing.Location
import Parsing.Syntax (RecFlag (..))
import qualified Parsing.Syntax as S
import Monad.QuipperError

import Control.Exception
import Data.List as List
import Data.Map (Map)

-- | The type of term and type variables. Each term or type variable is represented by a unique integer id.
type Variable = Int



-- | The type of referenced flags. A referenced flag represents a numbered flag variable. Three values are reserved:
--
-- *    0: the flag equal to zero (meaning not duplicable);
--
-- *    1: the flag equal to one (meaning duplicable);
--
-- *    -1: can be either zero or one, for example with types like /bool/ or /unit/,
--          which are implicitly equal to !/bool/ and !/unit/. Typically, flag 
--          constraints are dropped if their left-hand side or right-hand side is -1.
--
-- *    Any other value refers to a flag variable. For example, 2 means \"the second flag variable\".
type RefFlag = Int


-- | The flag 1.
one :: RefFlag
one = 1

-- | The flag 0.
zero :: RefFlag 
zero = 0


-- | The type of values a flag can take. Initially, all flags are set to 'Unknown', except
-- for some that are imposed to 'Zero' or 'One' by the typing rules.
data FlagValue =
    Unknown   -- ^ The value of the flag has not been decided yet.
  | One       -- ^ The value 1.
  | Zero      -- ^ The value 0.
  deriving Show

-- | Information relevant to a flag. This contains the flag value, and potentially some debug
-- information used to raise detailed exceptions. Eventually, it will also contain
-- various things such as reversibility, control, etc.
data FlagInfo = FInfo { 
  value :: FlagValue                              -- ^ The value of the flag.
}



-- $ The definition of types distinguishes between /linear types/ and
-- /types/.  Linear types are never duplicable, whereas types are
-- always annotated with an exponential flag. The grammar defines
-- linear types and types by mutual recursion. This ensures that types
-- are annotated with a flag in every possible place, but that flags
-- are never doubled up. This helps simplify the type inference algorithm.

-- | The type of linear type expressions. Linear types can never be
-- duplicable.
data LinType =
-- Basic types
    TVar Variable              -- ^ Type variable: /a/.
  | TArrow Type Type           -- ^ Function type: @T -> U@.

-- Tensor types
  | TUnit                      -- ^ Unit type: @()@.
  | TTensor [Type]             -- ^ Tensor product: @(T1 * .. * T/n/)@.

-- Sum types
  | TBool                      -- ^ The basic type /bool/.
  | TInt                       -- ^ The basic type /int/.
  | TUser Variable [Type]      -- ^ Algebraic type, parameterized over the variables /a/1 ... /an/.

-- Quantum related types
  | TQubit                     -- ^ The basic type /qubit/.
  | TCirc Type Type            -- ^ The type @circ (T, U)@.
  deriving (Show, Eq)


-- | The type of type expressions, which are linear types annotated
-- with a flag. This data type also includes /type schemes/, which
-- are used for polymorphism.
data Type =
    TBang RefFlag LinType                                  -- ^ The type @!^n A@.
  | TForall [RefFlag] [Variable] ConstraintSet Type        -- ^ A type scheme. This is a type with universally quantified type variables /a/1, ..., /a//n/ and
                                                           -- flags /f/1, ..., /f//k/, which must satisfy a set of constraints /L/.
  deriving Show


-- | Return the top-level annotation flag of a 'Type'.
top_flag :: Type -> RefFlag  
top_flag (TBang f _) = f
top_flag (TForall _ _ _ t) = top_flag t


-- | String the quantifiers from a 'Type'.
strip_forall :: Type -> (RefFlag, LinType)
strip_forall (TBang f t) = (f, t)
strip_forall (TForall _ _ _ t) = strip_forall t


-- | Remove the flag annotation from a type, returning a linear type.
-- This function does not make sense on typing schemes, and can only
-- be applied to types. It is an error to do otherwise.
no_bang :: Type -> LinType
no_bang (TBang _ t) = t
no_bang (TForall _ _ _ _) = throw $ ProgramError "no_bang: cannot be applied to a type scheme"

-- | Check whether a linear type uses algebraic data types.
is_user_lintype :: LinType -> Bool
is_user_lintype (TUser _ _) = True
is_user_lintype (TCirc t u) = is_user_type t || is_user_type u
is_user_lintype (TTensor tlist) = List.or $ List.map is_user_type tlist
is_user_lintype (TArrow t u) = is_user_type t || is_user_type u
is_user_lintype _ = False


-- | Check whether a type uses algebraic data types. This function can
-- only be applied to types. It is an error to apply it to a typing
-- scheme.
is_user_type :: Type -> Bool
is_user_type (TBang _ a) = is_user_lintype a
is_user_type (TForall _ _ _ _) = throw $ ProgramError "is_user_type: cannot be applied to a type scheme"



-- | An algebraic data type definition.
data Typedef = Typedef {
  d_args :: Int,                                             -- ^ The number of type arguments required.

  d_qdatatype :: Bool,                                       -- ^ Is this a quantum data type? Note that this flag is subject to change depending on the value of the type arguments.
                                                             -- Its precise meaning is: assuming the type arguments are quantum data types, then the whole type is a quantum data type.
                                                             -- For example, \"list a\" is a quantum data type on the condition that \"a\" is itself a quantum data type.

  d_unfolded :: ([Type], [(Datacon, Type)]),                 -- ^ The unfolded definition of the type. The left component is the list of type arguments, and the right component is the unfolded type:
                                                             -- a list of tuples (/Dk/, /Tk/) where /Dk/ is the name of the data constructor, /Tk/ is its type.

  d_subtype :: ([Type], [Type], ConstraintSet)               -- ^ The result of breaking the constraint {user args <: user args'}. This extension to the subtyping relation
                                                             -- is automatically inferred during the translation into the core syntax.
}



-- | A type synonym definition, e.g., @intlist@ = @list int@.
data Typesyn = Typesyn {
  s_args :: Int,                                             -- ^ The number of type arguments.

  s_qdatatype :: Bool,                                       -- ^ Is this a synonym of a quantum data type?

  s_unfolded :: Type                                         -- ^ The unfolded type.

  -- No subtyping relation is required, since the synonyms are automatically replaced.
}


-- | Like term and type variables, data constructors are attributed unique ids.
type Datacon = Int


-- | A core pattern.  The definition is largely the same as that of
-- the 'Parsing.Syntax.Pattern's of the surface syntax. The only
-- difference lies in variables, which are now represented by ids.
-- Although the syntax of Proto-Quipper does not make use of patterns,
-- keeping them as syntactic sugar reduces the number of variables,
-- since the desugaring process produces new variables, one for each
-- pair in the pattern. Here is how these patterns could be desugared:
-- 
-- >   fun p -> e             ==   fun x -> let p = x in e  (and desugar again)
-- >
-- >   let (p, q) = e in f    ==   If p, q are variables, then this is a structure of the language.
-- >                               Otherwise, use the code:
-- >                                    let (x, y) = e in
-- >                                    let p = x in
-- >                                    let q = y in
-- >                                    e
-- >                               (and desugar again).
--
-- Note that the expression @let x = e in f@ (where /x/ is a
-- variable), is not syntactic sugar.  It differs from the application
-- @(fun x -> f) e@ by the presence of let-polymorphism.
data Pattern =
    PWildcard                                          -- ^ The \"wildcard\" pattern: \"@_@\". This pattern matches any value, and the value is to be discarded.
  | PUnit                                           -- ^ Unit pattern: @()@.
  | PBool Bool                                      -- ^ Boolean pattern: @true@ or @false@.
  | PInt Int                                        -- ^ Integer pattern.
  | PVar Variable                                   -- ^ Variable pattern: /x/.
  | PTuple [Pattern]                                -- ^ Tuple pattern: @(/p/1, ..., /p//n/)@. By construction, must have /n/ >= 2.
  | PDatacon Datacon (Maybe Pattern)                -- ^ Data constructor pattern: \"@Datacon@\" or \"@Datacon /pattern/@\".
  | PLocated Pattern Extent                         -- ^ A located pattern.
  | PConstraint Pattern (S.Type, Map String Type)   -- ^ Constraint pattern: @(p <: T)@.
  deriving Show 


-- | Core patterns are located objects.
instance Located Pattern where
  location _ = Nothing
  locate p _ = p
  locate_opt p _ = p

  clear_location (PLocated p _) = clear_location p
  clear_location (PTuple plist) = PTuple $ List.map clear_location plist
  clear_location (PDatacon dcon (Just p)) = PDatacon dcon $ Just (clear_location p)
  clear_location (PConstraint p t) = PConstraint (clear_location p) t
  clear_location p = p

instance Constraint Pattern where
  drop_constraints (PConstraint p _) = drop_constraints p
  drop_constraints (PTuple plist) = PTuple $ List.map drop_constraints plist
  drop_constraints (PDatacon dcon (Just p)) = PDatacon dcon $ Just (drop_constraints p)
  drop_constraints (PLocated p ex) = PLocated (drop_constraints p) ex
  drop_constraints p = p


-- | A core expression. The core syntax introduces global variables, which are imported from imported modules.
-- Since the global variables are supposed to be duplicable, it is not necessary to overload the typing context with
-- more variables that are duplicable anyway.
data Expr =
-- STLC
    EVar Variable                                 -- ^ Variable: /x/.
  | EGlobal Variable                              -- ^ Global variable from the imported modules.
  | EFun Pattern Expr                             -- ^ Function abstraction: @fun p -> t@.
  | EApp Expr Expr                                -- ^ Function application: @t u@.

-- Introduction of the tensor
  | EUnit                                         -- ^ Unit term: @()@.
  | ETuple [Expr]                                 -- ^ Tuple: @(/t/1, .. , /t//n/)@. By construction, must have /n/ >= 2.
  | ELet RecFlag Pattern Expr Expr                -- ^ Let-binding: @let [rec] p = e in f@.

-- Custom union types
  | EBool Bool                                    -- ^ Boolean constant: @true@ or @false@.
  | EInt Int                                      -- ^ Integer constant.
  | EIf Expr Expr Expr                            -- ^ Conditional: @if e then f else g@.
  | EDatacon Datacon (Maybe Expr)                 -- ^ Data constructor: @Datacon e@. The argument is optional. The data constructors are considered and manipulated as values.
  | EMatch Expr [(Pattern, Expr)]                 -- ^ Case distinction: @match e with (p1 -> f1 | .. | pn -> fn)@.

-- Quantum rules
  | EBox Type                                     -- ^ The constant @box[T]@.
  | EUnbox                                        -- ^ The constant @unbox@.
  | ERev                                          -- ^ The constant @rev@.

-- Unrelated
  | ELocated Expr Extent                          -- ^ A located expression.
  | EBuiltin String                               -- ^ Built-in primitive: @#builtin s@.
  | EConstraint Expr (S.Type, Map String Type)    -- ^ Expression with type constraint: @(e <: T)@.
  | EError String                                 -- ^ User error.
  deriving Show



instance PPrint RefFlag where
  genprint _ f _ = pprint f

  sprintn _ 0 = ""
  sprintn _ 1 = "!"
  sprintn _ (-1) = ""
  sprintn _ (-2) = "?"
  sprintn _ n = supervar '!' n

  sprint n = sprintn defaultLvl n
  pprint n = sprintn Inf n


-- | The class of objects whose type is \'kind\'. Instances include, of course, 'LinType' and 'Type', but also
-- everything else that contains types: 'TypeConstraint', 'ConstraintSet', ['TypeConstraint'], etc.
-- The only purpose of this class is to overload the functions listed below.
class KType a where
  -- | Return the list of free type variables.
  free_typ_var :: a -> [Int]

  -- | Substitute a linear type for a type variable.
  subs_typ_var :: Int -> LinType -> a -> a
  
  -- | Return the list of flag references.
  free_flag :: a -> [Int]

  -- | Replace a flag reference for another one.
  subs_flag :: Int -> Int -> a -> a


instance KType LinType where
  free_typ_var (TVar x) = [x]
  free_typ_var (TTensor tlist) = List.foldl (\fv t -> List.union (free_typ_var t) fv) [] tlist
  free_typ_var (TArrow t u) = List.union (free_typ_var t) (free_typ_var u)
  free_typ_var (TCirc t u) = List.union (free_typ_var t) (free_typ_var u)
  free_typ_var (TUser _ arg) = List.foldl (\fv t -> List.union (free_typ_var t) fv) [] arg
  free_typ_var _ = []


  subs_typ_var a b (TVar x) | x == a = b
                        | otherwise = TVar x
  subs_typ_var _ _ TUnit = TUnit
  subs_typ_var _ _ TInt = TInt
  subs_typ_var _ _ TBool = TBool
  subs_typ_var _ _ TQubit = TQubit
  subs_typ_var a b (TUser n args) = TUser n $ List.map (subs_typ_var a b) args
  subs_typ_var a b (TArrow t u) = TArrow (subs_typ_var a b t) (subs_typ_var a b u)
  subs_typ_var a b (TTensor tlist) = TTensor $ List.map (subs_typ_var a b) tlist
  subs_typ_var a b (TCirc t u) = TCirc (subs_typ_var a b t) (subs_typ_var a b u)


  free_flag (TTensor tlist) = List.foldl (\fv t -> List.union (free_flag t) fv) [] tlist
  free_flag (TArrow t u) = List.union (free_flag t) (free_flag u)
  free_flag (TCirc t u) = List.union (free_flag t) (free_flag u)
  free_flag (TUser _ arg) = List.foldl (\fv t -> List.union (free_flag t) fv) [] arg
  free_flag _ = []


  subs_flag n m (TUser typename args) = TUser typename $ List.map (subs_flag n m) args
  subs_flag n m (TArrow t u) = TArrow (subs_flag n m t) (subs_flag n m u)
  subs_flag n m (TTensor tlist) = TTensor $ List.map (subs_flag n m) tlist
  subs_flag n m (TCirc t u) = TCirc (subs_flag n m t) (subs_flag n m u)
  subs_flag _ _ t = t



instance KType Type where
  free_typ_var (TBang _ t) = free_typ_var t
  free_typ_var (TForall _ _ _ t) = free_typ_var t
  subs_typ_var a b (TBang n t) = TBang n (subs_typ_var a b t)
  subs_typ_var a b (TForall _ _ _ _) = throw $ ProgramError "Type:subs_typ_var: cannot be applied to a type scheme"

  free_flag (TBang n t) = List.insert n (free_flag t)
  free_flag (TForall _ _ _ _) = throw $ ProgramError "Type:free_flag: cannot be applied to a type scheme"
  
  subs_flag n m (TBang p t) =
    let t' = subs_flag n m t in
    if n == p then
      TBang m t'
    else
      TBang p t'
  subs_flag n m (TForall _ _ _ _) = throw $ ProgramError "Type:subs_flag: cannot be applied to a type scheme"
  



-- | Equality of types must take into account alpha equivalence in the polymorphic types.
instance Eq Type where
  (==) (TBang m t) (TBang n t') = m == n && t == t'
  -- Normally, the alpha equivalence would have to be checked. However, it may
  -- be useless as: this function is never used, the generic instance is always the same, never
  -- changed.
  (==) (TForall _ _ _ typ) (TForall _ _ _ typ') = typ == typ'
  (==) _ _ = False


instance Param Pattern where
  free_var (PVar x) = [x]
  free_var (PDatacon _ Nothing) = []
  free_var (PDatacon _ (Just p)) = free_var p
  free_var (PTuple plist) = List.foldl (\fv p -> List.union (free_var p) fv) [] plist
  free_var (PConstraint p _) = free_var p
  free_var (PLocated p _) = free_var p
  free_var _ = []

  subs_var _ _ p = p


instance Param Expr where
  free_var (EVar x) = [x]
  
  free_var (EGlobal x) = [x]

  free_var (EFun p e) = 
    let fve = free_var e
        fvp = free_var p in
    fve \\ fvp

  free_var (ELet r p e f) =
    let fve = free_var e
        fvf = free_var f
        fvp = free_var p in
    (List.union fve fvf) \\ fvp

  free_var (EApp e f) =
    List.union (free_var e) (free_var f)

  free_var (ETuple elist) =
    List.foldl (\fv e -> List.union (free_var e) fv) [] elist

  free_var (EIf e f g) =
    List.union (List.union (free_var e) (free_var f)) (free_var g)

  free_var (EDatacon _ Nothing) = []
  free_var (EDatacon _ (Just e)) = free_var e

  free_var (EMatch e blist) =
    let fvlist = List.foldl (\fv (p, f) ->
                               List.union (free_var f \\ free_var p) fv) [] blist
        fve = free_var e in
    List.union fve fvlist
  
  free_var (ELocated e _) =
    free_var e

  free_var (EConstraint e _) =
    free_var e

  free_var _ =
    []

  subs_var _ _ e = e



-- | Determine whether an expression is a value or not.
is_value :: Expr -> Bool
is_value (ELocated e _) = is_value e
is_value (EFun _ _) = True
is_value (ETuple elist) = List.and $ List.map is_value elist
is_value (EBool _) = True
is_value (EInt _) = True
is_value (EDatacon _ e) = case e of
                            Nothing -> True
                            Just e -> is_value e
is_value (EBuiltin _) = True
is_value (EConstraint e _) = is_value e
is_value EUnbox = True
is_value (EBox _) = True
is_value ERev = True
is_value EUnit = True

is_value _ = False



-- | Information about a constraint. This includes the original
-- expression, location, and orientation (which side of the constraint
-- is the actual type). It is used in type constraints and flag
-- constraints.
data ConstraintInfo = Info {
  expression :: Expr,      -- ^ The original expression.
  loc :: Extent,           -- ^ The location of the original expression.
  actual :: Bool,          -- ^ The orientation of the constraint: true means actual type is on the left.
  in_type :: Maybe Type    -- ^ The original type (actual type before reducing).
} deriving Show


-- | An empty 'ConstraintInfo' structure.
no_info :: ConstraintInfo
no_info = Info {
  expression = EUnit,
  loc = extent_unknown,
  actual = True,
  in_type = Nothing
}



-- | The subtyping relation @<:@ operates on both linear types and types.
-- However, only constraints on types are kept, since it is the kind of constraints generated by the
-- constraint typing algorithm, and it is also useful to have the flag references at hand.
data TypeConstraint =
    Subtype Type Type ConstraintInfo              -- ^ A sub-typing constraint T <: U.
  | Sublintype LinType LinType ConstraintInfo     -- ^ A sub-typing constraint A <: B.
  deriving Show

instance Eq TypeConstraint where
  (==) (Subtype t u _) (Subtype t' u' _) = t == t' && u == u'
  (==) (Sublintype a b _) (Sublintype a' b' _) = a == a' && b == b'
  (==) _ _ = False


-- | A useful operator for writing sub-typing constraints.
(<:) :: Type -> Type -> TypeConstraint
t <: u = Subtype t u no_info                              


-- | A useful operator for writing a set of constraints of the form @T1, ..., Tn <: U@.
(<<:) :: [Type] -> Type -> [TypeConstraint]
tlist <<: u = List.map (\t -> t <: u) tlist


-- | A useful operator for writing a set of constraints of the form @T <: U1 .. Un@.
(<::) :: Type -> [Type] -> [TypeConstraint]
t <:: ulist = List.map (\u -> t <: u) ulist



-- | The type of /flag constraints/, which are constraints of the form n <= m. Their interpretation is as follows:
--
-- *  (n <= 0)     ==     (n :=: 0)
--
-- *  (1 <= n)     ==     (n :=: 1)
--
-- *  (m \<= n)     ==     (m = 1 =\> n = 1)
data FlagConstraint =
   Le RefFlag RefFlag ConstraintInfo
  deriving Show

instance Eq FlagConstraint where
  (==) (Le n m _) (Le n' m' _) = n == n' && m == m'


-- | A constraint set contains both subtyping and flag constraints.
type ConstraintSet =
  ([TypeConstraint], [FlagConstraint])


-- | The equality of constraint sets, allowing for substitutions of the constraints.
equals_set :: ConstraintSet -> ConstraintSet -> Bool
equals_set (lc, fc) (lc', fc') = (lc \\ lc' == []) && (lc' \\ lc == []) && (fc \\ fc' == []) && (fc' \\ fc == [])


-- | A type class for objects (such as constraints and constraint
-- sets) that carry debug information.  The purpose of this class is
-- to overload the operator (&), which appends debug information to
-- objects.
class WithDebugInfo a where
  -- | Append debug information to an object.
  (&) :: a -> ConstraintInfo -> a

instance WithDebugInfo [TypeConstraint] where
  cset & info = List.map (\c -> case c of
                            Sublintype a b _ -> Sublintype a b info
                            Subtype t u _ -> Subtype t u info) cset

instance WithDebugInfo [FlagConstraint] where
  cset & info = List.map (\(Le n m _) -> (Le n m info)) cset

instance WithDebugInfo ConstraintSet where
  (lc, fc) & info = (lc & info, fc & info)


-- | A type class for constraint \'sets\': the only three instances are 'FlagConstraint', 'TypeConstraint', and 'ConstraintSet'.
-- The purpose of this class is to overload the @\<\>@ operator to be able to use it on either constraint
-- sets, lists of type constraints, or lists of flag constraints.
class Constraints a b where
  -- ^ Concatenate two constraint sets. This function does not check for duplicates.
  (<>) :: a -> b -> ConstraintSet

instance Constraints [TypeConstraint] [TypeConstraint] where
  lc <> lc' = (lc ++ lc', [])

instance Constraints [TypeConstraint] [FlagConstraint] where
  lc <> fc = (lc, fc)

instance Constraints [TypeConstraint] ConstraintSet where
  lc <> (lc', fc') = (lc ++ lc', fc')

instance Constraints [FlagConstraint] [TypeConstraint] where
  fc <> lc = (lc, fc)

instance Constraints [FlagConstraint] [FlagConstraint] where
  fc <> fc' = ([], fc ++ fc')

instance Constraints [FlagConstraint] ConstraintSet where
  fc <> (lc', fc') = (lc', fc ++ fc')

instance Constraints ConstraintSet [TypeConstraint] where
  (lc, fc) <> lc' = (lc ++ lc', fc)

instance Constraints ConstraintSet [FlagConstraint] where
  (lc, fc) <> fc' = (lc, fc ++ fc')

instance Constraints ConstraintSet ConstraintSet where
  (lc, fc) <> (lc', fc') = (lc ++ lc', fc ++ fc')


-- | The empty constraint set.
emptyset :: ConstraintSet
emptyset = ([], [])


-- | Return true iff the constraint is of the form T <: T.
is_trivial :: TypeConstraint -> Bool
is_trivial (Subtype t u _) = t == u
is_trivial (Sublintype a b _) = a == b


-- | Return true iff the constraint /T/ <: /U/ is atomic, meaning
-- /T/ and /U/ are both of the form !^/n/ /a/, where /a/ is a type variable.
is_atomic :: TypeConstraint -> Bool
is_atomic (Sublintype (TVar _) (TVar _) _) = True
is_atomic _ = False


-- | Return true iff the constraint /T/ <: /U/ is composite, meaning
-- it can be reduced by application of one or more of the subtyping
-- relations.
is_composite :: TypeConstraint -> Bool
is_composite c = (not $ is_atomic c) && (not $ is_semi_composite c)


-- | Return true iff the constraint /T/ <: /U/ is semi-composite. This means
-- it is not atomic, and either /T/ or /U/ is of the form !^/n/ /a/, making it not
-- composite.
is_semi_composite :: TypeConstraint -> Bool
is_semi_composite (Sublintype t u _) =
  case (t, u) of
    (TVar _, TVar _) -> False
    (TVar _, _) -> True
    (_, TVar _) -> True
    _ -> False
is_semi_composite _ = False


-- | Return true iff the constraint is of the form (user /n/ /a/ <: user /n/ /a/').
is_user :: TypeConstraint -> Bool
is_user (Sublintype t u _) =
  case (t, u) of
    (TUser _ _, TUser _ _) -> True
    _ -> False
is_user _ = False

-- | Check whether the constraints of a list are either all right-sided or all left-sided. Here, a constraint is
--
-- * /left-sided/ if it is of the form /a/ <: /T/, and
--
-- * /right-sided/ if it is of the form /T/ <: /a/.
is_one_sided :: [TypeConstraint] -> Bool
is_one_sided [] = True
is_one_sided ((Sublintype t u _):cset) =
  case (t, u) of
    (TVar _, _) -> is_left_sided cset
    (_, TVar _) -> is_right_sided cset
    _ -> False
is_one_sided _ = False


-- | Check whether all the type constraints of a list are left-sided.
is_left_sided :: [TypeConstraint] -> Bool
is_left_sided [] = True
is_left_sided ((Sublintype (TVar _) _ _):cset) =
  is_left_sided cset
is_left_sided _ = False


-- | Check whether all the type constraints of a list are right-sided.
is_right_sided :: [TypeConstraint] -> Bool
is_right_sided [] = True
is_right_sided ((Sublintype _ (TVar _) _):cset) =
  is_right_sided cset
is_right_sided _ = False


-- | Attempt to link together the input constraints. For example the set { /b/ <: /U/, /a/ <: /b/, /T/ <: /a/ } can
--  be rearranged as { /T/ <: /a/ <: /b/ <: /U/ }.
--
--  The result is used in the unification algorithm: if the constraints can be linked, the approximation
--    { /T/ \<: /a/ \<: /b/ \<: /U/ }  \<=\>  /a/ :=: /b/ :=: /T/, { /T/ \<: /U/ } can be made.
chain_constraints :: [TypeConstraint] -> (Bool, [TypeConstraint])
chain_constraints l =
  case List.find (\c -> case c of
                          Sublintype (TVar _) _ _ -> False
                          _ -> True) l of
    Just c -> case c of
                Sublintype _ (TVar y) _ -> chain_left_to_right [c] y (List.delete c l)
                _ -> error "Unreduced composite constraint"
  
    Nothing -> case List.find (\c -> case c of
                                       Sublintype _ (TVar _) _ -> False
                                       _ -> True) l of
                 Just c -> case c of
                             Sublintype (TVar y) _ _ -> chain_right_to_left [c] y (List.delete c l)
                             _ -> error "Unreduced composite constraint"
                 Nothing -> error "Only atomic constraints"



-- | Try linking the constraints, starting from the left, and progressing by adding constraints
-- on the right.
chain_left_to_right :: [TypeConstraint] -> Int -> [TypeConstraint] -> (Bool, [TypeConstraint])
chain_left_to_right chain endvar [] = (True, List.reverse chain)
chain_left_to_right chain endvar l =
  case List.find (\c -> case c of
                          Sublintype (TVar y) _ _ -> y == endvar
                          _ -> False) l of
    Just c -> case c of
                Sublintype (TVar _) (TVar y) _ -> chain_left_to_right (c:chain) y (List.delete c l)
                _ -> if List.length l == 1 then
                       (True, List.reverse (c:chain))
                     else
                       (False, [])
    Nothing -> (False, [])


-- | Try linking the constraints, starting from the right, and progressing by adding constraints
-- on the left.
chain_right_to_left :: [TypeConstraint] -> Int -> [TypeConstraint] -> (Bool, [TypeConstraint])
chain_right_to_left chain endvar [] = (True, chain)
chain_right_to_left chain endvar l =
  case List.find (\c -> case c of
                          Sublintype _ (TVar y) _ -> y == endvar
                          _ -> False) l of
    Just c -> case c of
                Sublintype (TVar y) (TVar _) _ -> chain_right_to_left (c:chain) y (List.delete c l)
                _ -> if List.length l == 1 then
                       (True, c:chain)
                     else
                       (False, [])
    Nothing -> (False, [])



-- | Type constraints are an instance of 'KType'.
instance KType TypeConstraint where
  free_typ_var (Sublintype t u _) = List.union (free_typ_var t) (free_typ_var u)
  free_typ_var (Subtype t u _) = List.union (free_typ_var t) (free_typ_var u)
  subs_typ_var a b (Sublintype t u info) = Sublintype (subs_typ_var a b t) (subs_typ_var a b u) info
  subs_typ_var a b (Subtype t u info) = Subtype (subs_typ_var a b t) (subs_typ_var a b u) info

  free_flag (Sublintype t u _) = List.union (free_flag t) (free_flag u)
  free_flag (Subtype t u _) = List.union (free_flag t) (free_flag u)
  subs_flag n m (Sublintype t u info) = Sublintype (subs_flag n m t) (subs_flag n m u) info
  subs_flag n m (Subtype t u info) = Subtype (subs_flag n m t) (subs_flag n m u) info


-- | Constraint sets are an instance of 'KType'.
instance KType ConstraintSet where
  free_typ_var (lc, _) = List.foldl (\fv c -> List.union (free_typ_var c) fv) [] lc
  subs_typ_var a b (lc, fc) = (List.map (subs_typ_var a b) lc, fc)

  free_flag (lc, fc) =
    let ffl = List.foldl (\fv c -> List.union (free_flag c) fv) [] lc
        fff = List.foldl (\fv (Le n m _) -> List.union [n, m] fv) [] fc in
    List.union ffl fff 

  subs_flag n m (lc, fc) =
    let lc' = List.map (subs_flag n m) lc
        fc' = List.map (\(Le p q info) -> if p == n then (Le m q info)
                                   else if q == n then (Le p m info)
                                   else (Le p q info)) fc in
    (lc', fc')


-- | Generalize a type, associated with constraints, over its free variables and flags.
-- The free variables of the type are those that are greater or equal to a limit type\/flag.
generalize_type :: Type -> (Variable, RefFlag) -> ConstraintSet -> Type
generalize_type typ (limtype, limflag) cset =
  -- Free variables and flags of the type
  let fvt = free_typ_var typ
      fft = free_flag typ in

  -- Filter the bound variables
  let fvt' = List.filter (\x -> x >= limtype) fvt
      fft' = List.filter (\f -> f >= limflag) fft in

  -- An optimisation would separate the constraints relevant
  -- to the type before generalizing, but later
  TForall fft' fvt' cset typ



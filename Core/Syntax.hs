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
module Core.Syntax where

import Classes hiding ((\\))
import Utils

import Parsing.Location
import qualified Parsing.Syntax as S
import Monad.QuipperError

import qualified Compiler.SimplSyntax as C

import Control.Exception
import Data.List as List
import Data.Map (Map)

-- ----------------------------------------------------------------------
-- * Types

-- ----------------------------------------------------------------------
-- ** Flags

-- | The type of referenced flags. A referenced flag represents a numbered flag variable. Three values are reserved:
--
-- *    0: the flag equal to zero (meaning not duplicable);
--
-- *    1: the flag equal to one (meaning duplicable);
--
-- *    Any other value refers to a flag variable. For example, 2 means \"the second flag variable\".
type RefFlag = Int


-- | The flag 1.
one :: RefFlag
one = 1

-- | The flag 0.
zero :: RefFlag
zero = 0


instance PPrint RefFlag where
  genprint _ _ f = pprint f

  sprintn _ 0 = ""
  sprintn _ 1 = "!"
  sprintn _ n = "(" ++ show n ++ ")"



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
  f_value :: FlagValue                              -- ^ The value of the flag.
}

-- ----------------------------------------------------------------------
-- ** Types

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
    TVar Variable                -- ^ Type variable: /a/.
  | TArrow Type Type             -- ^ Function type: @T -> U@.

-- Tensor types
  | TUnit                        -- ^ Unit type: @()@.
  | TTensor [Type]               -- ^ Tensor product: @(T1 * .. * T/n/)@.

-- Sum types
  | TBool                        -- ^ The basic type /bool/.
  | TInt                         -- ^ The basic type /int/.
  | TAlgebraic Algebraic [Type]  -- ^ Algebraic type, parameterized over the variables /a1/ ... /an/.

-- Quantum related types
  | TQubit                       -- ^ The basic type /qubit/.
  | TCirc Type Type              -- ^ The type @circ (T, U)@.

-- Others
  | TSynonym Synonym [Type]      -- ^ Type synonym, parametrized over the variables /a1/ ... /an/.
  deriving (Show, Eq)


-- | The type of type expressions, which are linear types annotated
-- with a flag.
data Type =
  TBang RefFlag LinType      -- ^ The type @!^n A@.
  deriving (Show, Eq)


-- | An alternate definition of the equality between types. This function, contrarily to the default equality,
-- compares only the skeleton of the types, ignoring the flag variables.
eq_skel :: Type -> Type -> Bool
eq_skel (TBang _ (TArrow t u)) (TBang _ (TArrow t' u')) = eq_skel t t' && eq_skel u u'
eq_skel (TBang _ (TCirc t u)) (TBang _ (TCirc t' u')) = eq_skel t t' && eq_skel u u'
eq_skel (TBang _ (TTensor tlist)) (TBang _ (TTensor ulist)) =
  if List.length tlist == List.length ulist then
    List.and $ List.map (\(t, u) -> eq_skel t u) (List.zip tlist ulist)
  else
    False
eq_skel (TBang _ (TAlgebraic alg arg)) (TBang _ (TAlgebraic alg' arg')) =
  if alg == alg' && List.length arg == List.length arg' then
    List.and $ List.map (\(a, a') -> eq_skel a a') (List.zip arg arg')
  else
    False
eq_skel (TBang _ t) (TBang _ u) = t == u


-- | A type is concrete if it doesn't contain any type variables.
is_concrete :: Type -> Bool
is_concrete typ =
  free_typ_var typ == []


-- | The type of type schemes. A /type scheme/ is a type expression
-- together with universally quantified type variables /a/1, ...,
-- /a//n/ and flags /f/1, ..., /f//k/, which must satisfy a set of
-- constraints /L/.
data TypeScheme =
  TForall [RefFlag] [Variable] ConstraintSet Type
  deriving Show


-- | Convert a type to a trivial type scheme, i.e., without adding
-- quantifiers or constraints.
typescheme_of_type :: Type -> TypeScheme
typescheme_of_type t = TForall [] [] emptyset t


-- | Extract the main type of a typescheme (without instantiating it).
type_of_typescheme :: TypeScheme -> Type
type_of_typescheme (TForall _ _ _ t) = t


-- | Remove the flag annotation from a type, returning a linear type.
-- This function does not make sense on typing schemes, and can only
-- be applied to types. It is an error to do otherwise.
no_bang :: Type -> LinType
no_bang (TBang _ t) = t


instance KType TypeScheme where
  free_typ_var _ = []
  subs_typ_var _ _ a = a
  free_flag _ = []
  subs_flag _ _ a = a
  is_fun (TForall _ _ _ t) = is_fun t
  is_qdata (TForall _ _ _ t) = is_qdata t
  is_algebraic (TForall _ _ _ t) = is_algebraic t
  is_synonym _ = False




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


  -- | Return @True@ iff the argument is of the form \A -> B\.
  is_fun :: a -> Bool

  -- | Return @True@ iff the argument is a quantum data type.
  is_qdata :: a -> Bool

  -- | Return @True@ iff the argument is an algebraic type.
  is_algebraic :: a -> Bool

  -- | Return @True@ iff the argument is a type synonym.
  -- This function is optinal (default is False).
  is_synonym :: a -> Bool

  is_synonym _ = False


instance KType LinType where
  free_typ_var (TVar x) = [x]
  free_typ_var (TTensor tlist) = List.foldl (\fv t -> List.union (free_typ_var t) fv) [] tlist
  free_typ_var (TArrow t u) = List.union (free_typ_var t) (free_typ_var u)
  free_typ_var (TCirc t u) = List.union (free_typ_var t) (free_typ_var u)
  free_typ_var (TAlgebraic _ arg) = List.foldl (\fv t -> List.union (free_typ_var t) fv) [] arg
  free_typ_var (TSynonym _ arg) = List.foldl (\fv t -> List.union (free_typ_var t) fv) [] arg
  free_typ_var _ = []

  subs_typ_var a b (TVar x) | x == a = b
                        | otherwise = TVar x
  subs_typ_var _ _ TUnit = TUnit
  subs_typ_var _ _ TInt = TInt
  subs_typ_var _ _ TBool = TBool
  subs_typ_var _ _ TQubit = TQubit
  subs_typ_var a b (TAlgebraic n args) = TAlgebraic n $ List.map (subs_typ_var a b) args
  subs_typ_var a b (TSynonym n args) = TSynonym n $ List.map (subs_typ_var a b) args
  subs_typ_var a b (TArrow t u) = TArrow (subs_typ_var a b t) (subs_typ_var a b u)
  subs_typ_var a b (TTensor tlist) = TTensor $ List.map (subs_typ_var a b) tlist
  subs_typ_var a b (TCirc t u) = TCirc (subs_typ_var a b t) (subs_typ_var a b u)

  free_flag (TTensor tlist) = List.foldl (\fv t -> List.union (free_flag t) fv) [] tlist
  free_flag (TArrow t u) = List.union (free_flag t) (free_flag u)
  free_flag (TCirc t u) = List.union (free_flag t) (free_flag u)
  free_flag (TAlgebraic _ arg) = List.foldl (\fv t -> List.union (free_flag t) fv) [] arg
  free_flag _ = []

  subs_flag n m (TAlgebraic typename args) = TAlgebraic typename $ List.map (subs_flag n m) args
  subs_flag n m (TArrow t u) = TArrow (subs_flag n m t) (subs_flag n m u)
  subs_flag n m (TTensor tlist) = TTensor $ List.map (subs_flag n m) tlist
  subs_flag n m (TCirc t u) = TCirc (subs_flag n m t) (subs_flag n m u)
  subs_flag _ _ t = t

  is_fun (TArrow _ _) = True
  is_fun _ = False

  is_qdata TQubit = True
  is_qdata TUnit = True
  is_qdata (TTensor tlist) = List.and $ List.map is_qdata tlist
  is_qdata _ = False

  is_algebraic (TAlgebraic _ _) = True
  is_algebraic _ = False



instance KType Type where
  free_typ_var (TBang _ t) = free_typ_var t
  subs_typ_var a b (TBang n t) = TBang n (subs_typ_var a b t)

  free_flag (TBang n t) = List.insert n (free_flag t)

  subs_flag n m (TBang p t) =
    let t' = subs_flag n m t in
    if n == p then
      TBang m t'
    else
      TBang p t'

  is_fun (TBang _ t) = is_fun t
  is_algebraic (TBang _ t) = is_algebraic t
  is_qdata (TBang _ t) = is_qdata t
  is_synonym (TBang _ t) = is_synonym t


-- ----------------------------------------------------------------------
-- ** Data type definitions


-- | Describe the variability of an argument.
data Variance =
    Unrelated         -- ^ No clue.
  | Covariant         -- ^ The argument is covariant.
  | Contravariant     -- ^ The argument is contravariant.
  | Equal             -- ^ The argument is both covariant and contravariant.
  deriving Eq


instance Show Variance where
  show Unrelated = ""
  show Equal = "="
  show Covariant = "+"
  show Contravariant = "-"


-- | Return the least precise indication of the two arguments.
join :: Variance -> Variance -> Variance
join Unrelated v = v
join v Unrelated = v
join Covariant Contravariant = Equal
join Contravariant Covariant = Equal
join Covariant _ = Covariant
join _ Covariant = Covariant
join Contravariant _ = Contravariant
join _ Contravariant = Contravariant
join _ _ = Equal


-- Return the opposite variance.
opposite :: Variance -> Variance
opposite Covariant = Contravariant
opposite Contravariant = Covariant
opposite var = var



-- | An algebraic data type definition.
data Typedef = Typedef {
  d_args :: [Variance],                                      -- ^ The variance of each type argument.

  d_qdatatype :: Bool,                                       -- ^ Is this a quantum data type? Note that this flag is subject to change depending on the value of the type arguments.
                                                             -- Its precise meaning is: assuming the type arguments are quantum data types, then the whole type is a quantum data type.
                                                             -- For example, \"list a\" is a quantum data type on the condition that \"a\" is itself a quantum data type.

  d_unfolded :: ([Type], [(Datacon, Maybe Type)]),           -- ^ The unfolded definition of the type. The left component is the list of type arguments, and the right component is the unfolded type:
                                                             -- a list of tuples (/Dk/, /Tk/) where /Dk/ is the name of the data constructor, /Tk/ the type of its optinal argument.

  d_gettag :: Variable -> C.Expr                             -- ^ The extraction of the tag is common to all the constructors of an algebraic type.
}

-- ----------------------------------------------------------------------
-- ** Type synonyms

-- | A type synonym definition, e.g., @intlist@ = @list int@.
data Typesyn = Typesyn {
  s_args :: Int,                                             -- ^ The number of type arguments.

  s_qdatatype :: Bool,                                       -- ^ Is this a synonym of a quantum data type?

  s_unfolded :: ([Type], Type)                               -- ^ The unfolded type (given some argument types).

  -- No subtyping relation is required, since the synonyms are automatically replaced.
}


-- ----------------------------------------------------------------------
-- ** Data constructors



-- | A data constructor definition.
data Datacondef = Datacondef {
  d_datatype :: Variable,                                    -- ^ The original data type.

  d_type :: TypeScheme,                                      -- ^ The type of the constructor.

  d_tag :: Int,                                              -- ^ A tag (local to the type definition) uniquely identifying each constructor.

  d_ref :: Variable,                                         -- ^ Data constructors with one argument must define a function representing the constructor used without its argument.
                                                             -- For example, take the constructor \'Just\': a function is defined with the body
                                                             -- @ fun x -> Just x @
                                                             -- This variable records the name of definition of this function.
  d_construct :: Either C.Expr (C.Expr -> C.Expr),           -- ^ The implementation of a data constructor.
  d_deconstruct :: Variable -> C.Expr                        -- ^ The deconstructor associated with a data constrcuctor.
}


-- ----------------------------------------------------------------------
-- ** Global references

-- | The type of global references. Each expression / pattern is given one of those.
type Ref = Int

-- | The information contained by the above references.
data RefInfo = RInfo {
  r_location :: Extent,                -- ^ The extent of the expression in a file.
  r_expression :: Either Expr Pattern, -- ^ The referenced expression.
  r_type :: Type                      -- ^ The type of the expression.
}

-- ----------------------------------------------------------------------
-- ** Patterns

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
    PWildcard Ref                                       -- ^ The \"wildcard\" pattern: \"@_@\". This pattern matches any value, and the value is to be discarded.
  | PUnit Ref                                          -- ^ Unit pattern: @()@.
  | PBool Ref Bool                                      -- ^ Boolean pattern: @true@ or @false@.
  | PInt Ref Int                                        -- ^ Integer pattern.
  | PVar Ref Variable                                   -- ^ Variable pattern: /x/.
  | PTuple Ref [Pattern]                                -- ^ Tuple pattern: @(/p/1, ..., /p//n/)@. By construction, must have /n/ >= 2.
  | PDatacon Ref Datacon (Maybe Pattern)                -- ^ Data constructor pattern: \"@Datacon@\" or \"@Datacon /pattern/@\".
  | PConstraint Pattern (S.Type, Map String Type)   -- ^ Constraint pattern: @(p <: T)@.
  deriving Show


instance Constraint Pattern where
  drop_constraints (PConstraint p _) = drop_constraints p
  drop_constraints (PTuple ref plist) = PTuple ref $ List.map drop_constraints plist
  drop_constraints (PDatacon ref dcon (Just p)) = PDatacon ref dcon $ Just (drop_constraints p)
  drop_constraints p = p

instance Param Pattern where
  free_var (PVar _ x) = [x]
  free_var (PDatacon _ _ Nothing) = []
  free_var (PDatacon _ _ (Just p)) = free_var p
  free_var (PTuple _ plist) = List.foldl (\fv p -> List.union (free_var p) fv) [] plist
  free_var (PConstraint p _) = free_var p
  free_var _ = []

  subs_var _ _ p = p

-- ----------------------------------------------------------------------
-- * Expressions

-- | A core expression. The core syntax introduces global variables, which are imported from imported modules.
-- Since the global variables are supposed to be duplicable, it is not necessary to overload the typing context with
-- more variables that are duplicable anyway.
data Expr =
-- STLC
    EVar Ref Variable                                 -- ^ Variable: /x/.
  | EGlobal Ref Variable                              -- ^ Global variable from the imported modules.
  | EFun Ref Pattern Expr                             -- ^ Function abstraction: @fun p -> t@.
  | EApp Ref Expr Expr                                -- ^ Function application: @t u@.

-- Introduction of the tensor
  | EUnit Ref                                         -- ^ Unit term: @()@.
  | ETuple Ref [Expr]                                 -- ^ Tuple: @(/t/1, .. , /t//n/)@. By construction, must have /n/ >= 2.
  | ELet Ref RecFlag Pattern Expr Expr                -- ^ Let-binding: @let [rec] p = e in f@.

-- Custom union types
  | EBool Ref Bool                                    -- ^ Boolean constant: @true@ or @false@.
  | EInt Ref Int                                      -- ^ Integer constant.
  | EIf Ref Expr Expr Expr                            -- ^ Conditional: @if e then f else g@.
  | EDatacon Ref Datacon (Maybe Expr)                 -- ^ Data constructor: @Datacon e@. The argument is optional. The data constructors are considered and manipulated as values.
  | EMatch Ref Expr [(Pattern, Expr)]                 -- ^ Case distinction: @match e with (p1 -> f1 | .. | pn -> fn)@.

-- Quantum rules
  | EBox Ref Type                                     -- ^ The constant @box[T]@.
  | EUnbox Ref                                        -- ^ The constant @unbox@.
  | ERev Ref                                          -- ^ The constant @rev@.

-- Unrelated
  | EBuiltin Ref String                               -- ^ Built-in primitive: @#builtin s@.
  | EConstraint Expr (S.Type, Map String Type)        -- ^ Expression with type constraint: @(e <: T)@.
  deriving Show


instance Constraint Expr where
  drop_constraints (EFun ref p e) = EFun ref (drop_constraints p) (drop_constraints e)
  drop_constraints (EApp ref e f) = EApp ref (drop_constraints e) (drop_constraints f)
  drop_constraints (ETuple ref elist) = ETuple ref (List.map drop_constraints elist)
  drop_constraints (ELet ref r p e f) = ELet ref r (drop_constraints p) (drop_constraints e) (drop_constraints f)
  drop_constraints (EIf ref e f g) = EIf ref (drop_constraints e) (drop_constraints f) (drop_constraints g)
  drop_constraints (EDatacon ref dcon (Just e)) = EDatacon ref dcon $ Just (drop_constraints e)
  drop_constraints (EMatch ref e blist) = EMatch ref (drop_constraints e) (List.map (\(p, f) -> (drop_constraints p, drop_constraints f)) blist)
  drop_constraints (EConstraint e _) = drop_constraints e
  drop_constraints e = e


-- | Return the reference of an expression.
reference :: Expr -> Ref
reference (EVar ref _) = ref
reference (EGlobal ref _) = ref
reference (EFun ref _ _) = ref
reference (EApp ref _ _) = ref
reference (EUnit ref) = ref
reference (ETuple ref _) = ref
reference (ELet ref _ _ _ _) = ref
reference (EBool ref _) = ref
reference (EInt ref _) = ref
reference (EIf ref _ _ _) = ref
reference (EDatacon ref _ _) = ref
reference (EMatch ref _ _) = ref
reference (EBox ref _) = ref
reference (EUnbox ref) = ref
reference (ERev ref) = ref
reference (EBuiltin ref _) = ref
reference (EConstraint e _) = reference e


instance Param Expr where
  free_var (EVar _ x) = [x]

  free_var (EGlobal _ x) = [x]

  free_var (EFun _ p e) =
    let fve = free_var e
        fvp = free_var p in
    fve \\ fvp

  free_var (ELet _ r p e f) =
    let fve = free_var e
        fvf = free_var f
        fvp = free_var p in
    (List.union fve fvf) \\ fvp

  free_var (EApp _ e f) =
    List.union (free_var e) (free_var f)

  free_var (ETuple _ elist) =
    List.foldl (\fv e -> List.union (free_var e) fv) [] elist

  free_var (EIf _ e f g) =
    List.union (List.union (free_var e) (free_var f)) (free_var g)

  free_var (EDatacon _ _ Nothing) = []
  free_var (EDatacon _ _ (Just e)) = free_var e

  free_var (EMatch _ e blist) =
    let fvlist = List.foldl (\fv (p, f) ->
                               List.union (free_var f \\ free_var p) fv) [] blist
        fve = free_var e in
    List.union fve fvlist

  free_var (EConstraint e _) =
    free_var e

  free_var _ =
    []

  subs_var _ _ e = e



-- | Determine whether an expression is a value or not.
is_value :: Expr -> Bool
is_value (EFun _ _ _) = True
is_value (ETuple _ elist) = List.and $ List.map is_value elist
is_value (EBool _ _) = True
is_value (EInt _ _) = True
is_value (EDatacon _ _ e) = case e of
                            Nothing -> True
                            Just e -> is_value e
is_value (EBuiltin _ _) = True
is_value (EConstraint e _) = is_value e
is_value (EUnbox _) = True
is_value (EBox _ _) = True
is_value (ERev _) = True
is_value (EUnit _) = True

is_value _ = False


-- ----------------------------------------------------------------------
-- * Module declarations.

-- | Type of the module declarations. Once the type definitions have been taken care of,
-- there remains only top-level expressions and declarations.
data Declaration =
    DExpr Expr                   -- ^ A top-level expression.
  | DLet RecFlag Variable Expr   -- ^ A top-level declaration.


-- ----------------------------------------------------------------------
-- * Subtyping constraints.

-- | Information about a constraint. This includes the original
-- expression, location, and orientation (which side of the constraint
-- is the actual type). It is used in type constraints and flag
-- constraints.
data ConstraintInfo = CInfo {
  c_ref :: Ref,            -- ^ The reference of the expression / pattern from which originated the constraint.
  c_actual :: Bool,        -- ^ The orientation of the constraint: true means actual type is on the left.
  c_type :: Maybe Type     -- ^ The original type (actual type before reducing).
} deriving Show


-- | An empty 'ConstraintInfo' structure.
no_info :: ConstraintInfo
no_info = CInfo {
  c_ref = 0,
  c_actual = True,
  c_type = Nothing
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

  -- | Return @True@ if @t@ and @u@ from the constraint @t <: u@ are function types.
  is_fun (Sublintype t u _) = is_fun t && is_fun u
  is_fun (Subtype t u _) = is_fun t && is_fun u

  -- | Return @True@ if @t@ and @u@ from the constraint @t <: u@ are quantum data types.
  is_qdata (Sublintype t u _) = is_qdata t && is_qdata u
  is_qdata (Subtype t u _) = is_qdata t && is_qdata u

  -- | Return @True@ if @t@ and @u@ from the constraint @t <: u@ are algebraic types.
  is_algebraic (Sublintype t u _) = is_algebraic t && is_algebraic u
  is_algebraic (Subtype t u _) = is_algebraic t && is_algebraic u

  -- | Return @True@ if either @t@ or @u@ from the constraint @t <: u@ is a type synonym.
  is_synonym (Sublintype t u _) = is_synonym t || is_synonym u
  is_synonym (Subtype t u _) = is_synonym t || is_synonym u


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

  -- Not implemented.
  is_fun _ = False

  -- Not implemented.
  is_qdata _ = False

  -- Not implemented.
  is_algebraic _ = False

  -- Not implemented.
  is_synonym _ = False



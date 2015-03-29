{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}


-- | This module defines the /internal syntax/ of Proto-Quipper. Compared to the /surface syntax/
-- defined in "Parsing.Syntax", the grammar of types has been considerably modified to facilitate
-- type inference. For greater efficiency, all term and type variables are labelled by a unique id,
-- which serves as a lookup key in maps and other data structures.
module Core.Syntax where

import Classes hiding ((\\))
import Utils

import Parsing.Location
import qualified Parsing.Syntax as S

import Monad.Error

import qualified Compiler.SimplSyntax as C

import Data.List as List
import Data.IntSet as IntSet
import Data.Map (Map)
import Data.IntMap as IntMap


-- ----------------------------------------------------------------------
-- * Types

-- ----------------------------------------------------------------------
-- ** Flags

-- | The type of referenced flags. A referenced flag represents a numbered flag variable. Three
-- values are reserved:
--
-- *    0: the flag equal to zero (meaning not duplicable);
--
-- *    1: the flag equal to one (meaning duplicable);
--
-- *    Any other value refers to a flag variable.
type Flag = Int


-- | The flag 1.
one :: Flag
one = 1

-- | The flag 0.
zero :: Flag
zero = 0


-- ----------------------------------------------------------------------
-- ** Types

-- $ The definition of types distinguishes between /linear types/ and /types/.  Linear types are
-- never duplicable, whereas types are always annotated with an exponential flag. The grammar defines
-- linear types and types by mutual recursion. This ensures that types are annotated with a flag in
-- every possible place, but that flags are never doubled up. This helps simplify the type inference
-- algorithm.


-- | Type constructors. Type constructors are of two kinds: predefined types, and user-defined types.
-- NB: -> could be defined in the core library, because it admits a constant number of arguments,
-- but the tensor type is of polymorphic kind, and could not be defined so.
data ConstantType =
    TypeBuiltin String                -- ^ A named type constructor (includes "->", "*").
  | TypeUser Int                      -- ^ User defined type constructor.
  deriving (Show, Eq)

-- | The type of linear type expressions. Expressions with linear types can never be duplicable.
-- Linear types implement the standard type algebra, where the only objects are type variables,
-- type constructions (application) and some type constants.
data LinearType =
    TypeVar Variable                  -- ^ Type variables.
  | TypeApply ConstantType [Type]     -- ^ Constructed type.
  deriving (Show, Eq)


-- | The type of type expressions, which are linear types annotated with a flag. Since we want to
-- map type variables to types instead of linear types, type variables should not be considered linear
-- types.
data Type =
    TypeAnnot Flag LinearType         -- ^ The type @!^n A@.
  deriving (Show, Eq)


-- | An alternate definition of the equality between types. This function, contrarily to the default
-- equality, compares only the skeleton of the types, ignoring the flag variables.
equalsLinear :: Type -> Type -> Bool
equalsLinear (TypeAnnot _ (TypeApply c args)) (TypeAnnot _ (TypeApply c' args')) =
  if c == c' && List.length args == List.length args' then
    List.and $ List.map (\(t, t') -> equalsLinear t t') (List.zip args args')
  else False
equalsLinear (TypeAnnot _ t) (TypeAnnot _ t') = t == t'


-- | A type is concrete if it doesn't contain any type variables.
isConcrete :: Type -> Bool
isConcrete typ = IntSet.null $ freevar typ

-- | Remove the flag annotation from a type, returning a linear type.
unannot :: Type -> LinearType
unannot (TypeAnnot _ t) = t

-- | Build a constant type.
constant :: Flag -> String -> Type
constant flag name = TypeAnnot flag (TypeApply (TypeBuiltin name) [])

-- | Apply a type constructor to some arguments.
apply :: Flag -> String -> [Type] -> Type
apply flag name args = TypeAnnot flag (TypeApply (TypeBuiltin name) args)


-- *** Some predefined types. Those include: qubit, unit, int, bool, circ.

qubit :: Type
qubit = constant 0 "qubit"

unit :: Type
unit = constant 0 "unit"

int :: Type
int = constant 0 "int"

bool :: Type
bool = constant 0 "bool"

circ :: Type -> Type -> Type
circ t u = apply 1 "circ" [t, u]

-- | Build the type !1 T -> U.
arrow :: Type -> Type -> Type
arrow t u = apply 1 "->" [t, u]

-- | Build the type !1 T1 * .. * Tn.
tensor :: [Type] -> Type
tensor args = apply 1 "*" args


-- | Convert a regular type to a quantum data type.
quantumTypeOfType :: Type -> QuantumType
quantumTypeOfType (TypeAnnot _ (TypeApply (TypeBuiltin "unit") _)) = QUnit
quantumTypeOfType (TypeAnnot _ (TypeVar a)) = QVar a
quantumTypeOfType (TypeAnnot _ (TypeApply (TypeBuiltin "qubit") _)) = QQubit
quantumTypeOfType (TypeAnnot _ (TypeApply (TypeBuiltin "*") tuple)) =
  QTensor $ List.map quantumTypeOfType tuple
quantumTypeOfType _ = throwNE $ UserError "PatternElimination:quantumTypeOfType: illegal argument"

-- | Convert the type of an unbox operator (only) to 'Compiler.PatternElimination.QuantumType'.
-- An exception is raised if the given type is not of the form: @Circ (QuantumType, QuantumType) -> _@.
circuitTypeOfType :: Type -> CircuitType
circuitTypeOfType (TypeAnnot _ (TypeApply (TypeBuiltin "->") [t,_])) =
  case t of
    TypeAnnot _ (TypeApply (TypeBuiltin "circ") [t,u]) ->
      (quantumTypeOfType t, quantumTypeOfType u)
    _ -> throwNE $ UserError "PatternElimination:circuitTypeOfType: illegal argument"
circuitTypeOfType _ =
  throwNE $ UserError "PatternElimination:circuitTypeOfType: illegal argument"


-- | Bind two types, producing a mapping from type variables to types.
bindTypes :: Type -> Type -> IntMap Type
bindTypes t t' = bindTypesAux t t' IntMap.empty
  where
    bindTypesAux (TypeAnnot _ (TypeVar v)) typ map = IntMap.insert v typ map
    bindTypesAux (TypeAnnot _ (TypeApply c args)) (TypeAnnot _ (TypeApply c' args')) map =
      List.foldl (\map (t, t') -> bindTypesAux t t' map) map $ List.zip args args'
    bindTypesAux _ _ map = map


-- | Apply the binding produced by the function 'Core.Syntax.bindTypes'.
mapType :: IntMap Type -> Type -> Type
mapType b (TypeAnnot n (TypeVar v)) =
  case IntMap.lookup v b of
    Just t -> t
    Nothing -> TypeAnnot n $ TypeVar v
mapType b (TypeAnnot n (TypeApply c args)) =
  TypeAnnot n $ TypeApply c $ List.map (mapType b) args


-- | The type of type schemes. A /type scheme/ is a type expression together with universally
-- quantified type variables /a/1, ..., /a//n/ and flags /f/1, ..., /f//k/, which must satisfy a set
-- of constraints /L/.
data TypeScheme =
  TypeScheme [Flag] [Variable] ConstraintSet Type
  deriving Show


-- | Convert a type to a trivial type scheme, i.e., without adding
-- quantifiers or constraints.
schemeOfType :: Type -> TypeScheme
schemeOfType t = TypeScheme [] [] emptyset t

-- | Extract the main type of a typescheme (without instantiating it).
typeOfScheme :: TypeScheme -> Type
typeOfScheme (TypeScheme _ _ _ t) = t

-- Linear types.

instance Subs LinearType LinearType where
  subs x t (TypeVar x') | x == x' = t
                        | otherwise = TypeVar x'
  subs x t (TypeApply c args) = TypeApply c $ List.map (subs x t) args

instance Subs LinearType Variable where
  subs n m (TypeApply c args) = TypeApply c $ List.map (subs n m) args
  subs _ _ t = t

instance TermObject LinearType where
  freevar (TypeVar x) = IntSet.singleton x
  freevar (TypeApply _ args) = IntSet.unions $ List.map freevar args

instance TypeObject LinearType where
  freeflag (TypeVar _) = IntSet.empty
  freeflag (TypeApply _ args) = IntSet.unions $ List.map freeflag args

  isFunction (TypeApply (TypeBuiltin "->") _) = True
  isFunction _ = False

  isQuantum (TypeApply (TypeBuiltin "qubit") _) = True
  isQuantum (TypeApply (TypeBuiltin "circ") _) = True
  isQuantum (TypeApply (TypeBuiltin "unit") _) = True
  isQuantum (TypeApply (TypeBuiltin "*") args) = List.and $ List.map isQuantum args
  isQuantum _ = False

-- Types.

instance Subs Type LinearType where
  subs x t (TypeAnnot n u) = TypeAnnot n (subs x t u)

instance Subs Type Variable where
  subs n m (TypeAnnot n' t) =
    let t' = subs n m t in
    if n == n' then TypeAnnot m t'
    else TypeAnnot n' t'

instance TermObject Type where
  freevar (TypeAnnot _ t) = freevar t

instance TypeObject Type where
  freeflag (TypeAnnot n t) = IntSet.insert n (freeflag t)
  isFunction (TypeAnnot _ t) = isFunction t
  isQuantum (TypeAnnot _ t) = isQuantum t

-- Type schemes.

instance Subs TypeScheme LinearType where
  subs _ _ a = a

instance Subs TypeScheme Variable where
  subs _ _ a = a

instance TermObject TypeScheme where
  freevar _ = IntSet.empty

instance TypeObject TypeScheme where
  freeflag _ = IntSet.empty
  isFunction (TypeScheme _ _ _ t) = isFunction t
  isQuantum (TypeScheme _ _ _ t) = isQuantum t


-- ----------------------------------------------------------------------
-- ** Global references

-- | Genenral information about patterns or expressions.
data Info = Info {
  extent :: Extent,                                   -- ^ The extent of the expression in a file.
  typ :: Type                                         -- ^ The type of the expression.
} deriving Show

-- | Empty information.
noTermInfo :: Info
noTermInfo = Info { extent = unknownExtent, typ = unit }

-- ----------------------------------------------------------------------
-- ** Patterns

-- | A core pattern.  The definition is largely the same as that of the 'Parsing.Syntax.Pattern's of
-- the surface syntax. The only difference lies in variables, which are now represented by ids.
-- Although the syntax of Proto-Quipper does not make use of patterns, keeping them as syntactic
-- sugar reduces the number of variables, since the desugaring process produces new variables, one
-- for each pair in the pattern. Here is how these patterns could be desugared:
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
-- Note that the expression @let x = e in f@ (where /x/ is a variable), is not syntactic sugar. It
-- differs from the application @(fun x -> f) e@ by the presence of let-polymorphism.
data Pattern =
  -- | The \"wildcard\" pattern: \"@_@\". This pattern matches any value, and the value is to be discarded.
    PWildcard Info
  -- | Constant values (integers, booleans ..).
  | PConstant Info ConstantValue
  -- | Pattern variables: /x/.
  | PVar Info Variable
  -- | Tuple pattern: @(/p/1, ..., /p//n/)@. By construction, must have /n/ >= 2.
  | PTuple Info [Pattern]
  -- | Data constructor pattern: \"@Datacon@\" or \"@Datacon /pattern/@\".
  | PDatacon Info Datacon (Maybe Pattern)
  -- | Type coercion: @(p <: T)@. The type has not been converted yet.
  | PCoerce Pattern S.Type (Map String Type)
  deriving Show


instance Coerced Pattern where
  uncoerce (PCoerce p _ _) = uncoerce p
  uncoerce (PTuple ref tuple) = PTuple ref $ List.map uncoerce tuple
  uncoerce (PDatacon ref cons (Just p)) = PDatacon ref cons $ Just (uncoerce p)
  uncoerce p = p

instance TermObject Pattern where
  freevar (PVar _ x) = IntSet.singleton x
  freevar (PDatacon _ _ Nothing) = IntSet.empty
  freevar (PDatacon _ _ (Just p)) = freevar p
  freevar (PTuple _ tuple) = IntSet.unions $ List.map freevar tuple
  freevar (PCoerce p _ _) = freevar p
  freevar _ = IntSet.empty


-- | Return information about a pattern.
patternInfo :: Pattern -> Info
patternInfo (PVar i _) = i
patternInfo (PDatacon i _ _) = i
patternInfo (PTuple i _) = i
patternInfo (PConstant i _) = i
patternInfo (PWildcard i) = i
patternInfo (PCoerce p _ _) = patternInfo p


-- ----------------------------------------------------------------------
-- * Value bindings.

data Binding = Binding { binder :: Pattern, value :: Expr } deriving Show

instance TermObject Binding where
  freevar (Binding binder value) = (freevar value) IntSet.\\ (freevar binder)

instance Coerced Binding where
  uncoerce (Binding binder value) = Binding (uncoerce binder) (uncoerce value)

-- ----------------------------------------------------------------------
-- * Expressions

-- | A core expression. The core syntax introduces global variables, which are imported from imported
-- modules. Since the global variables are supposed to be duplicable, it is not necessary to overload
-- the typing context with more variables that are duplicable anyway.
data Expr =
  -- STLC.
    EVar Info Variable                                 -- ^ Variable: /x/.
  | EGlobal Info Variable                              -- ^ Global variable from the imported modules.
  | EFun Info Pattern Expr                             -- ^ Function abstraction: @fun p -> t@.
  | EApp Expr Expr                                     -- ^ Function application: @t u@.
  | ELet RecFlag Pattern Expr Expr                     -- ^ Let-binding: @let [rec] p = e in f@.

  -- Constants.
  | EConstant Info ConstantValue                       -- ^ Constant values (integers, booleans ..).

  -- Conditionnals and pattern matchings.
  | EIf Expr Expr Expr                                 -- ^ Conditional: @if e then f else g@.
  | EMatch Info Expr [Binding]                         -- ^ Case distinction: @match e with (p1 -> f1 | .. | pn -> fn)@.
  | EDatacon Info Datacon (Maybe Expr)                 -- ^ Data constructor: @Datacon e@. The argument is optional. The data constructors are considered and manipulated as values.
  | ETuple Info [Expr]                                 -- ^ Tuple: @(/t/1, .. , /t//n/)@. By construction, must have /n/ >= 2.

  -- Quantum rules
  | EBox Info Type                                     -- ^ The constant @box[T]@.
  | EUnbox Info                                        -- ^ The constant @unbox@.
  | ERev Info                                          -- ^ The constant @rev@.

  -- Unrelated
  | EError String                                     -- ^ Throw an error.
  | ECoerce Expr (S.Type, Map String Type)            -- ^ Expression with type constraint: @(e <: T)@.
  deriving Show


instance Coerced Expr where
  uncoerce (EFun ref p e) = EFun ref (uncoerce p) (uncoerce e)
  uncoerce (EApp e f) = EApp (uncoerce e) (uncoerce f)
  uncoerce (ETuple ref elist) = ETuple ref (List.map uncoerce elist)
  uncoerce (ELet r p e f) = ELet r (uncoerce p) (uncoerce e) (uncoerce f)
  uncoerce (EIf e f g) = EIf (uncoerce e) (uncoerce f) (uncoerce g)
  uncoerce (EDatacon ref dcon (Just e)) = EDatacon ref dcon $ Just (uncoerce e)
  uncoerce (EMatch info test cases) = EMatch info (uncoerce test) (List.map uncoerce cases)
  uncoerce (ECoerce e _) = uncoerce e
  uncoerce e = e

instance TermObject Expr where
  freevar (EVar _ x) = IntSet.singleton x
  freevar (EGlobal _ x) = IntSet.singleton x
  freevar (EFun _ arg body) = (freevar body) IntSet.\\ (freevar arg)
  freevar (ELet _ pat value body) =
    (IntSet.union (freevar value) (freevar body)) IntSet.\\ (freevar pat)
  freevar (EApp fun arg) = IntSet.union (freevar fun) (freevar arg)
  freevar (ETuple _ tuple) = IntSet.unions $ List.map freevar tuple
  freevar (EIf cond true false) = IntSet.unions [freevar cond, freevar true, freevar false]
  freevar (EDatacon _ _ Nothing) = IntSet.empty
  freevar (EDatacon _ _ (Just e)) = freevar e
  freevar (EMatch _ test cases) = IntSet.unions (freevar test : List.map (freevar) cases)
  freevar (ECoerce e _) = freevar e
  freevar _ = IntSet.empty


-- | Return information about an expression.
exprInfo :: Expr -> Info
exprInfo (ECoerce e _) = exprInfo e
exprInfo (EVar i _) = i
exprInfo (EGlobal i _) = i
exprInfo (EFun i _ _) = i
exprInfo (ETuple i _) = i
exprInfo (EDatacon i _ _) = i
exprInfo (EMatch i _ _) = i
exprInfo (EConstant i _) = i
exprInfo (ELet _ _ _ _) = Info { extent = unknownExtent, typ = unit }
exprInfo (EApp _ _) = Info { extent = unknownExtent, typ = unit }
exprInfo (EIf _ _ _) = Info { extent = unknownExtent, typ = unit }
exprInfo (EError _) = Info { extent = unknownExtent, typ = unit }
exprInfo (EBox i _) = i
exprInfo (EUnbox i) = i
exprInfo (ERev i) = i

-- | Determine whether an expression is a value or not.
isValue :: Expr -> Bool
isValue (EFun _ _ _) = True
isValue (ETuple _ tuple) = List.and $ List.map isValue tuple
isValue (EConstant _ _) = True
isValue (EDatacon _ _ e) =
  case e of
    Nothing -> True
    Just e -> isValue e
isValue (ECoerce e _) = isValue e
isValue (EUnbox _) = True
isValue (EBox _ _) = True
isValue (ERev _) = True
isValue _ = False


-- ----------------------------------------------------------------------
-- * Module declarations.

-- | Type of the module declarations. Once the type definitions have been taken care of,
-- there remains only top-level expressions and declarations.
data Declaration =
    DExpr Info Expr                   -- ^ A top-level expression.
  | DLet Info RecFlag Variable Expr   -- ^ A top-level declaration.


-- ----------------------------------------------------------------------
-- * Subtyping constraints.

-- | Expression at the source of a typing constraint.
data ConstraintSource =
    InExpr Expr
  | InPattern Pattern
  | Unidentified
  deriving Show


-- | Information about a constraint. This includes the original
-- expression, location, and orientation (which side of the constraint
-- is the actual type). It is used in type constraints and flag
-- constraints.
data ConstraintInfo = ConstraintInfo {
  actual :: Bool,        -- ^ The orientation of the constraint: true means actual type is on the left.
  sourceType :: Maybe Type,        -- ^ The original type (actual type before reducing).
  sourceExpr :: ConstraintSource   -- ^ The original expression / pattern.
} deriving Show


-- | An empty 'ConstraintInfo' structure.
noInfo :: ConstraintInfo
noInfo = ConstraintInfo {
  actual = True,
  sourceType = Nothing,
  sourceExpr = Unidentified
}


-- | The subtyping relation @<:@ operates on both linear types and types.
-- However, only constraints on types are kept, since it is the kind of constraints generated by the
-- constraint typing algorithm, and it is also useful to have the flag references at hand.
data TypeConstraint =
    Subtype Type Type ConstraintInfo              -- ^ A sub-typing constraint T <: U.
  | SubLinearType LinearType LinearType ConstraintInfo     -- ^ A sub-typing constraint A <: B.
  deriving Show

instance Eq TypeConstraint where
  (==) (Subtype t u _) (Subtype t' u' _) = t == t' && u == u'
  (==) (SubLinearType a b _) (SubLinearType a' b' _) = a == a' && b == b'
  (==) _ _ = False


-- | A useful operator for writing sub-typing constraints.
(<:) :: Type -> Type -> TypeConstraint
t <: u = Subtype t u noInfo

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
  Le { left :: Flag, right :: Flag, info :: ConstraintInfo }
  deriving Show

instance Eq FlagConstraint where
  (==) (Le n m _) (Le n' m' _) = n == n' && m == m'


-- | A constraint set contains both subtyping and flag constraints.
data ConstraintSet =
  ConstraintSet {
    typeConstraints :: [TypeConstraint],
    flagConstraints :: [FlagConstraint]
  }
  deriving Show


-- | A type class for objects (such as constraints and constraint
-- sets) that carry debug information.  The purpose of this class is
-- to overload the operator (&), which appends debug information to
-- objects.
class WithDebugInfo a where
  -- | Append debug information to an object.
  (&) :: a -> ConstraintInfo -> a

instance WithDebugInfo TypeConstraint where
  (Subtype t u _) & info = Subtype t u info
  (SubLinearType t u _) & info = SubLinearType t u info

instance WithDebugInfo [TypeConstraint] where
  cset & info = List.map (& info) cset

instance WithDebugInfo [FlagConstraint] where
  cset & info = List.map (\(Le n m _) -> (Le n m info)) cset

instance WithDebugInfo ConstraintSet where
  (ConstraintSet lc fc) & info = ConstraintSet (lc & info) (fc & info)


-- | A type class for constraint \'sets\': the only three instances are 'FlagConstraint', 'TypeConstraint',
-- and 'ConstraintSet'. The purpose of this class is to overload the @\<\>@ operator to be able to
-- use it on either constraint sets, lists of type constraints, or lists of flag constraints.
class Constraints a b where
  -- ^ Concatenate two constraint sets. This function does not check for duplicates.
  (<>) :: a -> b -> ConstraintSet

instance Constraints [TypeConstraint] [TypeConstraint] where
  lc <> lc' = ConstraintSet (lc ++ lc') []

instance Constraints [TypeConstraint] [FlagConstraint] where
  lc <> fc = ConstraintSet lc fc

instance Constraints [TypeConstraint] ConstraintSet where
  lc <> (ConstraintSet lc' fc) = ConstraintSet (lc ++ lc') fc

instance Constraints FlagConstraint ConstraintSet where
  f <> (ConstraintSet lc fc) = ConstraintSet lc $ f:fc

instance Constraints [FlagConstraint] [TypeConstraint] where
  fc <> lc = ConstraintSet lc fc

instance Constraints [FlagConstraint] [FlagConstraint] where
  fc <> fc' = ConstraintSet [] (fc ++ fc')

instance Constraints [FlagConstraint] ConstraintSet where
  fc <> (ConstraintSet lc fc') = ConstraintSet lc (fc ++ fc')

instance Constraints ConstraintSet [TypeConstraint] where
  (ConstraintSet lc fc) <> lc' = ConstraintSet (lc ++ lc') fc

instance Constraints ConstraintSet [FlagConstraint] where
  (ConstraintSet lc fc) <> fc' = ConstraintSet lc (fc ++ fc')

instance Constraints ConstraintSet ConstraintSet where
  (ConstraintSet lc fc) <> (ConstraintSet lc' fc') = ConstraintSet (lc ++ lc') (fc ++ fc')


-- | The empty constraint set.
emptyset :: ConstraintSet
emptyset = ConstraintSet [] []


-- | Return true iff the constraint is of the form T <: T.
--is_trivial :: TypeConstraint -> Bool
--is_trivial (Subtype t u _) = t == u
--is_trivial (SubLinearType a b _) = a == b


-- | Return true iff the constraint /T/ <: /U/ is atomic, meaning
-- /T/ and /U/ are both of the form !^/n/ /a/, where /a/ is a type variable.
--is_atomic :: TypeConstraint -> Bool
--is_atomic (SubLinearType (TypeVar _) (TypeVar _) _) = True
--is_atomic _ = False


-- | Return true iff the constraint /T/ <: /U/ is composite, meaning
-- it can be reduced by application of one or more of the subtyping
-- relations.
--is_composite :: TypeConstraint -> Bool
--is_composite c = (not $ is_atomic c) && (not $ is_semi_composite c)


-- | Return true iff the constraint /T/ <: /U/ is semi-composite. This means
-- it is not atomic, and either /T/ or /U/ is of the form !^/n/ /a/, making it not
-- composite.
--is_semi_composite :: TypeConstraint -> Bool
--is_semi_composite (SubLinearType t u _) =
--  case (t, u) of
--    (TypeVar _, TypeVar _) -> False
--    (TypeVar _, _) -> True
--    (_, TypeVar _) -> True
--    _ -> False
--is_semi_composite _ = False


-- | Check whether the constraints of a list are either all right-sided or all left-sided. Here, a constraint is
--
-- * /left-sided/ if it is of the form /a/ <: /T/, and
--
-- * /right-sided/ if it is of the form /T/ <: /a/.
is_one_sided :: [TypeConstraint] -> Bool
is_one_sided [] = True
is_one_sided ((SubLinearType t u _):cset) =
  case (t, u) of
    (TypeVar _, _) -> is_left_sided cset
    (_, TypeVar _) -> is_right_sided cset
    _ -> False
is_one_sided _ = False


-- | Check whether all the type constraints of a list are left-sided.
is_left_sided :: [TypeConstraint] -> Bool
is_left_sided [] = True
is_left_sided ((SubLinearType (TypeVar _) _ _):cset) =
  is_left_sided cset
is_left_sided _ = False


-- | Check whether all the type constraints of a list are right-sided.
is_right_sided :: [TypeConstraint] -> Bool
is_right_sided [] = True
is_right_sided ((SubLinearType _ (TypeVar _) _):cset) =
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
                          SubLinearType (TypeVar _) _ _ -> False
                          _ -> True) l of
    Just c -> case c of
                SubLinearType _ (TypeVar y) _ -> chain_left_to_right [c] y (List.delete c l)
                _ -> error "Unreduced composite constraint"

    Nothing -> case List.find (\c -> case c of
                                       SubLinearType _ (TypeVar _) _ -> False
                                       _ -> True) l of
                 Just c -> case c of
                             SubLinearType (TypeVar y) _ _ -> chain_right_to_left [c] y (List.delete c l)
                             _ -> error "Unreduced composite constraint"
                 Nothing -> error "Only atomic constraints"



-- | Try linking the constraints, starting from the left, and progressing by adding constraints
-- on the right.
chain_left_to_right :: [TypeConstraint] -> Int -> [TypeConstraint] -> (Bool, [TypeConstraint])
chain_left_to_right chain endvar [] = (True, List.reverse chain)
chain_left_to_right chain endvar l =
  case List.find (\c -> case c of
                          SubLinearType (TypeVar y) _ _ -> y == endvar
                          _ -> False) l of
    Just c -> case c of
                SubLinearType (TypeVar _) (TypeVar y) _ -> chain_left_to_right (c:chain) y (List.delete c l)
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
                          SubLinearType _ (TypeVar y) _ -> y == endvar
                          _ -> False) l of
    Just c -> case c of
                SubLinearType (TypeVar y) (TypeVar _) _ -> chain_right_to_left (c:chain) y (List.delete c l)
                _ -> if List.length l == 1 then
                       (True, c:chain)
                     else
                       (False, [])
    Nothing -> (False, [])


instance Subs TypeConstraint LinearType where
  subs a b (SubLinearType t u info) = SubLinearType (subs a b t) (subs a b u) info
  subs a b (Subtype t u info) = Subtype (subs a b t) (subs a b u) info

instance Subs TypeConstraint Variable where
  subs n m (SubLinearType t u info) = SubLinearType (subs n m t) (subs n m u) info
  subs n m (Subtype t u info) = Subtype (subs n m t) (subs n m u) info

instance TermObject TypeConstraint where
  freevar (SubLinearType t u _) = IntSet.union (freevar t) (freevar u)
  freevar (Subtype t u _) = IntSet.union (freevar t) (freevar u)

instance TypeObject TypeConstraint where
  freeflag (SubLinearType t u _) = IntSet.union (freeflag t) (freeflag u)
  freeflag (Subtype t u _) = IntSet.union (freeflag t) (freeflag u)

  -- | Return @True@ if @t@ and @u@ from the constraint @t <: u@ are function types.
  isFunction (SubLinearType t u _) = isFunction t && isFunction u
  isFunction (Subtype t u _) = isFunction t && isFunction u

  -- | Return @True@ if @t@ and @u@ from the constraint @t <: u@ are quantum data types.
  isQuantum (SubLinearType t u _) = isQuantum t && isQuantum u
  isQuantum (Subtype t u _) = isQuantum t && isQuantum u

instance Subs ConstraintSet LinearType where
  subs a b (ConstraintSet lc fc) = ConstraintSet (List.map (subs a b) lc) fc

instance Subs ConstraintSet Variable where
  subs n m (ConstraintSet lc fc) =
    let lc' = List.map (subs n m) lc
        fc' = List.map (\(Le p q info) -> if p == n then (Le m q info)
                                   else if q == n then (Le p m info)
                                   else (Le p q info)) fc in
    ConstraintSet lc' fc'

instance TermObject ConstraintSet where
  freevar (ConstraintSet lc _) = IntSet.unions $ List.map freevar lc

instance TypeObject ConstraintSet where
  freeflag (ConstraintSet lc fc) =
    let ffl = IntSet.unions $ List.map freevar lc
        fff = IntSet.unions $ List.map (\(Le n m _) -> IntSet.fromList [n,m]) fc in
    IntSet.union ffl fff

  -- Not implemented.
  isFunction _ = False
  -- Not implemented.
  isQuantum _ = False

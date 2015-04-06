-- | This module defines the /surface syntax/ of types, patterns, and expressions, as parsed by the
-- parser. This should not be confused with the /internal syntax/ defined in "Typer.CoreSyntax",
-- which is used internally by the interpreter and type checker.
module Parsing.Syntax where

import Classes
import Utils

import Parsing.Location

import Monad.Error

import Data.Char
import Data.Map
import Data.List as List

-- ----------------------------------------------------------------------
-- * Syntax

-- ----------------------------------------------------------------------
-- ** Declarations


-- | A generic description of type definition (algberaic and synonym).
data Typedef a = Typedef {
  name :: String,              -- ^ The name of the type.
  arguments :: [String],       -- ^ The list of type arguments.
  definition :: a              -- ^ The definition of the type.
}

-- | An algebraic data type definition.
type TypeAlgebraic = Typedef [(String, Maybe Type)]

-- | A type synonym definition, e.g., @intlist@ = @list int@.
type TypeAlias = Typedef Type


-- | A top-level declaration. A top-level declaration can be of four kinds:
--
-- * a top-level variable declaration;
--
-- * a top-level expression;
--
-- * a block of algebraic type definitions;
--
-- * a type synonym.
--
--
data Declaration =
    DLet Extent RecFlag XExpr XExpr                 -- ^ A variable declaration: @let p = e;;@.
  | DExpr Extent XExpr                              -- ^ A simple expression: @e;;@
  | DTypes [TypeAlgebraic]                   -- ^ A list of type definitions. The types are mutually recursive.
  | DSyn TypeAlias                           -- ^ A type synonym definition.


-- ----------------------------------------------------------------------
-- ** Programs

-- | A program (or equivalently, a module).
data Program = Program {
  moduleName :: String,       -- ^ Name of the module.
  filePath :: FilePath,       -- ^ Path to the implementation of the module.
  imports :: [String],        -- ^ List of imported modules.
  body :: [Declaration]       -- ^ Body of the module, which contains the type and term declarations.
}


-- | A dummy, empty program.
dummyProgram :: Program
dummyProgram = Program {
  moduleName = "Dummy",
  filePath = unknownFile,
  imports = [],
  body = []
}

-- | Modules are compared based on their name. This implies two different modules can't have the
-- same name.
instance Eq Program where
  (==) p1 p2 = moduleName p1 == moduleName p2


-- ----------------------------------------------------------------------
-- ** Types

-- | A type.
data Type =
-- STLC types
    TVar String               -- ^ Type variable: /a/, /b/, ...
  | TQualified String String  -- ^ Qualified type name: @Module.type@.
  | TArrow Type Type          -- ^ Function type: @A -> B@.

-- Tensor types
  | TUnit                     -- ^ Unit type: @()@.
  | TTensor [Type]            -- ^ Tensor product: @A1 * ... * A/n/@.

-- Flavour : duplicable flag
  | TBang Type                -- ^ Exponential type: @!A@.

-- Quantum related types
  | TQubit                    -- ^ The basic type /qubit/.
  | TCirc Type Type           -- ^ The type @circ (A, B)@.

-- Sum types: bool and generic type instantiation
  | TApp Type Type            -- ^ Application of a type constructor to a type argument. For example, \'list int\' is \'list\' applied to \'int\'.
  | TBool                     -- ^ The basic type /bool/.
  | TInt                      -- ^ The basic type /int/.

-- Generic types
  | TScheme String Type       -- ^ A type generalized over a single variable. This constructor is not readily accessible to the user.

-- Unrelated
  | TLocated Type Extent      -- ^ A located type.
  deriving Show


-- | Add an exponential (\"!\") annotation to a type. This first checks
-- whether the type is already of the form !/A/, so as to avoid duplicate exponentials
-- like !!/A/.
bang :: Type -> Type
bang (TLocated a ex) =
  TLocated (bang a) ex

bang (TBang a) =
  TBang a

bang a =
  TBang a


-- | When comparing types for equality, we ignore any location information associated with the types.
instance Eq Type where
  (==) (TLocated t1 _) t2 = t1 == t2
  (==) t1 (TLocated t2 _) = t1 == t2
  (==) (TVar x) (TVar y) = x == y
  (==) (TQualified m x) (TQualified m' x') = m == m' && x == x'
  (==) TUnit TUnit = True
  (==) TBool TBool = True
  (==) TInt TInt = True
  (==) TQubit TQubit = True
  (==) (TCirc t1 t2) (TCirc t1' t2') = (t1 == t1') && (t2 == t2')
  (==) (TTensor tlist) (TTensor tlist') = (tlist == tlist')
  (==) (TArrow t1 t2) (TArrow t1' t2') = (t1 == t1') && (t2 == t2')
  (==) (TBang t1) (TBang t2) = (t1 == t2)
  (==) _ _ = False


-- | Types are located objects.
instance Located Type where
  -- | Add location information to a type.
  locate (TLocated t ex) _ = TLocated t ex
  locate t ex = TLocated t ex

  -- | Return, if any, the location of the type.
  location (TLocated _ ex) = Just ex
  location _ = Nothing

  -- | Same as locate, with an optional argument.
  locate_opt t Nothing = t
  locate_opt t (Just ex) = locate t ex

  -- | Recursively removes the location annotations.
  clear_location (TLocated t _) = clear_location t
  clear_location (TCirc t u) = TCirc (clear_location t) (clear_location u)
  clear_location (TTensor tlist) = TTensor $ List.map clear_location tlist
  clear_location (TArrow t u) = TArrow (clear_location t) (clear_location u)
  clear_location (TBang t) = TBang (clear_location t)
  clear_location t = t



-- ------------------------------------------------------------------------------------------------
-- ** X-expressions

-- $ An /X-expression/ is an expression that may possibly contain wildcards. X-expressions are used
-- by the parser before they are converted either to expressions or to patterns.


-- | The type of X-expressions. The type argument /a/ determines whether wildcards are permitted or
-- not. If /a/ is non-empty, then wildcards are allowed. If /a/ is empty, wildcards are not allowed,
-- and therefore, 'XExpr' 'Empty' is just the type of ordinary expressions.

data XExpr =
  -- | A \"wildcard\": \"@_@\". This is only permitted when /a/ is non-empty, so actual expressions,
  -- which are of type 'XExpr' 'Empty', contain no wildcards. However, wildcards are temporarily
  -- permitted during parsing, for expressions that are to be converted to patterns.
    EWildcard

-- STLC
  | EVar String                    -- ^ Variable: @x@.
  | EQualified String String       -- ^ Qualified variable: @Path.Module.x@.
  | EFun XExpr XExpr               -- ^ Function abstraction: @fun p -> e@.
  | EApp XExpr XExpr               -- ^ Function application: @e f@.

-- Addition of tensors
  | ETuple [XExpr]                 -- ^ Tuple: @(/e/1, .., /en/)@. By construction, must have /n/ >= 2.
  | ELet RecFlag XExpr XExpr XExpr -- ^ Let-binding: @let [rec] p = e in f@.
  | EUnit                          -- ^ Unit term: @()@.

-- Addition of sum types
  | EDatacon String (Maybe XExpr)  -- ^ Data constructor: @String e@.
  | EMatch XExpr [(XExpr, XExpr)]  -- ^ Case distinction: @match e with (p1 -> f1 | p2 -> f2 | ... | pn -> fn)@.
  | EIf XExpr XExpr XExpr          -- ^ Conditional: @if e then f else g@
  | EBool Bool                     -- ^ Boolean constant: @true@ or @false@.
  | EInt Int                       -- ^ Integer constant.

-- Circuit construction
  | EBox Type                      -- ^ The constant @box[T]@.
  | EUnbox                         -- ^ The constant @unbox@.
  | ERev                           -- ^ The constant @rev@.

-- Unrelated
  | ECoerce XExpr Type             -- ^ Expression with type constraint: @(e <: A)@.
  | EError String                  -- ^ Throw an error.
  | ELocated XExpr Extent          -- ^ A located expression.
  deriving Show


-- | A version of the 'EFun' constructor that constructs an /n/-ary
-- function. We assume /n/ >= 1.
multi_EFun :: [XExpr] -> XExpr -> XExpr
multi_EFun [] e = e
multi_EFun (p:ps) e = EFun p (multi_EFun ps e)



-- | X-expressions are located objects.
instance Located XExpr where
  -- | Add some location information to an expression.
  locate (ELocated e ex) _ = ELocated e ex
  locate e ex = ELocated e ex

  -- | Return, if any given, the location of an expression.
  location (ELocated _ ex) = Just ex
  location _ = Nothing

  -- | Same as locate, with an optional argument.
  locate_opt e Nothing = e
  locate_opt e (Just ex) = locate e ex

  -- | Recursively removes all location annotations.
  clear_location (ELocated e _) = clear_location e
  clear_location (ECoerce e t) = ECoerce (clear_location e) t
  clear_location (EFun p e) = EFun (clear_location p) (clear_location e)
  clear_location (ELet r p e f) = ELet r (clear_location p) (clear_location e) (clear_location f)
  clear_location (EApp e f) = EApp (clear_location e) (clear_location f)
  clear_location (ETuple elist) = ETuple $ List.map clear_location elist
  clear_location (EIf e f g) = EIf (clear_location e) (clear_location f) (clear_location g)
  clear_location (EBox t) = EBox (clear_location t)
  clear_location (EDatacon dcon Nothing) = EDatacon dcon Nothing
  clear_location (EDatacon dcon (Just e)) = EDatacon dcon (Just $ clear_location e)
  clear_location (EMatch e plist) = EMatch (clear_location e) $ List.map (\(p, f) -> (clear_location p, clear_location f)) plist
  clear_location e = e


-- | Flatten an application of XExpr.
flatten :: XExpr -> (XExpr, [XExpr])
flatten e =
  let (p, arg) = aux e in
  (p, List.reverse arg)
    where
      -- Return the flattened expression, where the arguments list is reversed.
      aux (EApp e f) =
        let (p,es) = aux e in
        (p,f:es)
      aux (ELocated e ex) =
        case aux e of
          (e, []) -> (ELocated e ex, [])
          (e,arg) -> (e,arg)
      aux e =
        (e,[])


-- | Build a let-expression.
build_let :: RecFlag -> XExpr -> XExpr -> XExpr -> XExpr
build_let r e f g =
  case flatten e of
    (p, []) -> ELet r p f g
    (ELocated (EDatacon dcon Nothing) ex, [e]) ->
        ELet r (ELocated (EDatacon dcon $ Just e) ex) f g
    (p, arg) ->
        let f' = multi_EFun arg f in
        ELet r p f' g


-- | Build a let-declaration.
build_dlet :: Maybe Extent -> RecFlag -> XExpr -> XExpr -> Declaration
build_dlet loc r e f =
  let loc' = case loc of Just loc -> loc ; Nothing -> unknownExtent in
  let (p,arg) = flatten e
      f' = multi_EFun arg f in
  DLet loc' r p f'

buildToplevelExpr :: Maybe Extent -> XExpr -> Declaration
buildToplevelExpr loc e =
  case loc of
    Just loc -> DExpr loc e
    Nothing -> DExpr unknownExtent e

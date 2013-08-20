-- | This module defines the /surface syntax/ of types, patterns, and
-- expressions, as parsed by the parser. This should not be confused
-- with the /internal syntax/ defined in "Typing.CoreSyntax", which is
-- used internally by the interpreter and type checker.
module Parsing.Syntax where

import Classes

import Parsing.Location

import Data.Char
import Data.Map
import Data.List as List

-- | A data constructor. A data constructor is uniquely determined by its name.
type Datacon = String


-- | An algebraic data type definition.
data Typedef = Typedef {
  d_typename :: String,                        -- ^ Name of the defined type.
  d_args :: [String],                          -- ^ List of bound type arguments.
  d_constructors :: [(Datacon, Maybe Type)]    -- ^ List of data constructors, each given by the name of the constructor and the type of the optional argument.
}


-- | A type synonym definition, e.g., @intlist@ = @list int@.
data Typesyn = Typesyn {
  s_typename :: String,                        -- ^ Name of the defined type.
  s_args :: [String],                          -- ^ List of bound type arguments.
  s_synonym :: Type                            -- ^ The type it is a synonym of.
}


-- | A top-level declaration. A top-level declaration can be of four kinds:
--
-- * a top-level variable declaration;
-- 
-- * a top-level expression;
--
-- * a type definition;
--
-- * a type synonym.
--
-- 
data Declaration =
    DLet RecFlag Pattern Expr                -- ^ A variable declaration: @let x = e;;@.
  | DExpr Expr                               -- ^ A simple expression: @e;;@
  | DTypes [Typedef]                         -- ^ A list of type definitions. The types are mutually recursive.
  | DSyn Typesyn                             -- ^ A type synonym definition.



-- | A program (or equivalently, a module).
data Program = Prog {
-- Module name and file
  module_name :: String,                     -- ^ Name of the module.
  filepath :: FilePath,                      -- ^ Path to the implementation of the module.

-- Import declarations
  imports :: [String],                       -- ^ List of imported modules.
 
-- The body of the module
  body :: [Declaration],                     -- ^ Body of the module, which contains the type and term declarations. 

-- Optional interface
  interface :: Maybe Interface               -- ^ Optional interface file.
}


-- | A dummy program that is completely empty.
dummy_program :: Program
dummy_program = Prog {
  module_name = "Dummy",
  filepath = file_unknown,
  imports = [],
  body = [],
  interface = Nothing
}


-- | An interface file. This consists of a list of type declarations,
-- which must be a subset of the global variables of the module
-- implementation.
type Interface = [(String, Type)]


-- | Modules are compared based on their name.
-- This implies two different modules can't have the same name.
instance Eq Program where
  (==) p1 p2 = module_name p1 == module_name p2



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


-- | A pattern.
data Pattern =
    PJoker                               -- ^ The \"wildcard\" pattern: \"@_@\". This is also sometimes called the /joker/. This pattern matches any value, and the value is to be discarded.
                                         -- In Proto-Quipper, a wildcard can only match a duplicable value. 
  | PUnit                                -- ^ Unit pattern: @()@.
  | PVar String                          -- ^ Variable pattern: /x/.
  | PTuple [Pattern]                     -- ^ Tuple pattern: @(/p/1, ..., /p//n/)@. By construction, must have /n/ >= 2.
  | PDatacon Datacon (Maybe Pattern)     -- ^ Data constructor pattern: \"@Datacon@\" or \"@Datacon /pattern/@\".
  | PConstraint Pattern Type             -- ^ Constraint pattern: @(x <: A)@.
  | PLocated Pattern Extent              -- ^ A located pattern.
  deriving Show


-- | Patterns are located objects.
instance Located Pattern where
  -- | Add location information to a pattern.
  locate (PLocated p ex) _ = PLocated p ex
  locate p ex = PLocated p ex

  -- | Return, if any defined, the location of the pattern.
  location (PLocated _ ex) = Just ex
  location _ = Nothing

  -- | Same as locate, with an optional argument.
  locate_opt p Nothing = p
  locate_opt p (Just ex) = locate p ex

  -- | Recursively removes all location annotations.
  clear_location (PLocated p _) = clear_location p
  clear_location (PTuple plist) = PTuple $ List.map clear_location plist
  clear_location (PConstraint p t) = PConstraint (clear_location p) t
  clear_location p = p


-- | A recursive flag. This is used in the expression 'ELet' to indicate
-- whether the function is recursive or not. The parser only allows functions (and not arbitrary values)
-- to be declared recursive.
data RecFlag =
    Nonrecursive   -- ^ Non recursive binding.
  | Recursive      -- ^ Recursive binding.
  deriving (Show, Eq)


-- | A term.
data Expr =
-- STLC
    EVar String                    -- ^ Variable: /x/.
  | EQualified String String       -- ^ Qualified variable: @Module.x@.
  | EFun Pattern Expr              -- ^ Function abstraction: @fun p -> e@.
  | EApp Expr Expr                 -- ^ Function application: @e f@.

-- Addition of tensors
  | ETuple [Expr]                  -- ^ Tuple: @(/e/1, .., /en/)@. By construction, must have /n/ >= 2.
  | ELet RecFlag Pattern Expr Expr -- ^ Let-binding: @let [rec] p = e in f@.
  | EUnit                          -- ^ Unit term: @()@.

-- Addition of sum types
  | EDatacon String (Maybe Expr)   -- ^ Data constructor: @Datacon e@.
  | EMatch Expr [(Pattern, Expr)]  -- ^ Case distinction: @match e with (p1 -> f1 | p2 -> f2 | ... | pn -> fn)@.
  | EIf Expr Expr Expr             -- ^ Conditional: @if e then f else g@
  | EBool Bool                     -- ^ Boolean constant: @true@ or @false@.
  | EInt Int                       -- ^ Integer constant.

-- Circuit construction
  | EBox Type                      -- ^ The constant @box[T]@.
  | EUnbox                         -- ^ The constant @unbox@.
  | ERev                           -- ^ The constant @rev@.

-- Unrelated
  | EConstraint Expr Type          -- ^ Expression with type constraint: @(e <: A)@.
  | EBuiltin String                -- ^ Built-in primitive: @#builtin s@.
  | ELocated Expr Extent           -- ^ A located expression.
  deriving Show



-- | Expressions are located objects.
instance Located Expr where
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
  clear_location (EConstraint e t) = EConstraint (clear_location e) t
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



-- | Translate a pattern to the corresponding expression. For example, the pattern (/x/, /y/) is transformed
-- into the expression (/x/, /y/). Any location annotations are preserved.
expr_of_pattern :: Pattern -> Expr
expr_of_pattern PUnit = EUnit
expr_of_pattern (PVar x) = EVar x
expr_of_pattern (PTuple plist) = ETuple $ List.map expr_of_pattern plist
expr_of_pattern (PLocated p ex) = ELocated (expr_of_pattern p) ex


-- | The inverse of 'expr_of_pattern'. Translate an expression to the corresponding pattern. While
-- 'expr_of_pattern' always succeeds, 'pattern_of_expr' may fail if called on a term that is \"not a pattern\", for example,
-- a lambda abstraction. Any location annotations are preserved.
pattern_of_expr :: Expr -> Pattern
pattern_of_expr EUnit = PUnit
pattern_of_expr (EVar x) = PVar x
pattern_of_expr (ETuple elist) = PTuple $ List.map pattern_of_expr elist
pattern_of_expr (ELocated e ex) = PLocated (pattern_of_expr e) ex

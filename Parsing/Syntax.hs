-- | This module gives the definition of the syntax of the expressions as parsed by the parser.
-- It includes the syntax of types, patterns, and expressions.
module Parsing.Syntax where

import Classes

import Parsing.Localizing

import Data.Char
import Data.Map
import Data.List as List

-- | A data constructor defined by its name.
type Datacon = String


-- | Algebraic type definition.
data Typedef = Typedef {
  d_typename :: String,                        -- ^ Name of the type.
  d_args :: [String],                          -- ^ List of bound type arguments.
  d_constructors :: [(Datacon, Maybe Type)]    -- ^ List of data constructors, defined by the name of the constructor, and the type of the optional argument.
}


-- | Type synonyms, e.g., @intlist@ = @list int@.
data Typesyn = Typesyn {
  s_typename :: String,                        -- ^ Name of the type.
  s_args :: [String],                          -- ^ List of bound type arguments.
  s_synonym :: Type                            -- ^ Type it is synonym of.
}


-- | Toplevel declarations. They can be of four kinds:
--
-- * Type definitions
--
-- * Type synonyms
--
-- * Top-level expressions
--
-- * Top-level declarations
-- 
data Declaration =
    DLet RecFlag Pattern Expr                -- ^ Variable declaration : let x = e ;;
  | DExpr Expr                               -- ^ Simple expression    : e ;;
  | DTypes [Typedef]                         -- ^ A list of type definitions. All types are mutually inductive.
  | DSyn Typesyn                             -- ^ A type synonym



-- | Definition of a program (= module).
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


-- | A dummy program, all empty.
dummy_program :: Program
dummy_program = Prog {
  module_name = "Dummy",
  filepath = file_unknown,
  imports = [],
  body = [],
  interface = Nothing
}


-- | Definition of an interface file. The definition carries the list of type declarations contained in the interface, which
-- list must be a subset of the global variables of the implementation.
type Interface = [(String, Type)]


-- | Modules are compared based on their name.
-- This implies two different modules can't have the same name.
instance Eq Program where
  (==) p1 p2 = module_name p1 == module_name p2



-- | Definition of types.
data Type =
-- STLC types
    TVar String               -- ^ a, b, ..
  | TQualified String String  -- ^ Module.type
  | TArrow Type Type          -- ^ A -> B

-- Tensor types
  | TUnit                     -- ^ ()
  | TTensor [Type]            -- ^ A1 * .. * An

-- Flavour : duplicable flag
  | TBang Type                -- ^ !A

-- Quantum related types
  | TQubit                     -- ^ qubit
  | TCirc Type Type           -- ^ circ (A, B)

-- Sum types : bool and generic type instantiation
  | TApp Type Type            -- ^ Generic type instantiation, for example \'list int\' is \'int\' applied to \'list\'.
  | TBool                     -- ^ bool
  | TInt                      -- ^ int

-- Unrelated
  | TLocated Type Extent      -- ^ Located types
  deriving Show


-- | Add a bang annotation to a type, first checking whether the type was of the form !A or not to
-- avoid duplicate bangs like !!A.
bang :: Type -> Type
bang (TLocated a ex) =
  TLocated (bang a) ex

bang (TBang a) =
  TBang a

bang a =
  TBang a


-- | This instance declaration has to be written manually to ignore the location
-- associated to types when checking the equality. 
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


-- | Types are located objects
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



-- | Definition of patterns.
data Pattern =
    PJoker                               -- ^ _. Is called the joker, the wildcard .. It's an empty pattern used to signify that the value has to be discarded.
                                         -- It can be used in Proto-Quipper on the condition that it be duplicable.
  | PUnit                                -- ^ ()
  | PVar String                          -- ^ x
  | PTuple [Pattern]                     -- ^ (x1, .., xn). By construction, n must be >= 2.
  | PDatacon Datacon (Maybe Pattern)     -- ^ Datacon p
  | PConstraint Pattern Type             -- ^ (x <: A)
  | PLocated Pattern Extent              -- ^ Located patterns.
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


-- | Definition of a recursive flag, used in the expression ELet to indicate
-- whether the function is recursive or not. The parser only allows functions
-- to be declared recursive.
data RecFlag =
    Nonrecursive   -- ^ Non recursive binding.
  | Recursive      -- ^ Recursive binding.
  deriving (Show, Eq)


-- | Definition of terms.
data Expr =
-- STLC
    EVar String                    -- ^ x
  | EQualified String String       -- ^ Module.x
  | EFun Pattern Expr              -- ^ fun p -> e
  | EApp Expr Expr                 -- ^ e f

-- Addition of tensors
  | ETuple [Expr]                  -- ^ (e1, .., en). Same as patterns, n >= 2.
  | ELet RecFlag Pattern Expr Expr -- ^ let [rec] p = e in f
  | EUnit                          -- ^ ()

-- Addition of sum types
  | EDatacon String (Maybe Expr)   -- ^ Datacon e
  | EMatch Expr [(Pattern, Expr)]  -- ^ match e with (p1 -> f1 | p2 -> f2 | ... | pn -> fn)
  | EIf Expr Expr Expr             -- ^ if e then f else g
  | EBool Bool                     -- ^ true / false
  | EInt Int                       -- ^ Integers

-- Circuit construction
  | EBox Type                      -- ^ box[T]
  | EUnbox                         -- ^ unbox
  | ERev                           -- ^ rev

-- Unrelated
  | EConstraint Expr Type          -- ^ (e <: A)
  | EBuiltin String                -- ^ #builtin s
  | ELocated Expr Extent           -- ^ Located expressions.
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



-- | Translates an pattern into the corresponding expression. For example, the pattern (x, y) is transformed
-- into the expression (x, y) (...). The location annotations are conserved.
expr_of_pattern :: Pattern -> Expr
expr_of_pattern PUnit = EUnit
expr_of_pattern (PVar x) = EVar x
expr_of_pattern (PTuple plist) = ETuple $ List.map expr_of_pattern plist
expr_of_pattern (PLocated p ex) = ELocated (expr_of_pattern p) ex


-- | Function reverse of expr_of_pattern: translates an expression into the corresponding pattern. When
-- expr_of_pattern was sure to succeed, this one may fail if called on something \"not a pattern\" : for example
-- a lambda abstraction. The locations are conserved.
pattern_of_expr :: Expr -> Pattern
pattern_of_expr EUnit = PUnit
pattern_of_expr (EVar x) = PVar x
pattern_of_expr (ETuple elist) = PTuple $ List.map pattern_of_expr elist
pattern_of_expr (ELocated e ex) = PLocated (pattern_of_expr e) ex

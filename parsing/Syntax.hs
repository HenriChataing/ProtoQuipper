module Syntax where

import Localizing
import Classes

import Data.Char
import Data.Map
import Data.List as List

-- | A data constructor is defined by its name
type Datacon = String


-- | Type declarations
-- For now, types takes no type argument
-- The definition is a list of pairs datacon * generic type variables * type
data Typedef = Typedef String [String] [(Datacon, Maybe Type)]



-- | Declarations
data Declaration =
    DLet RecFlag Pattern Expr
  | DExpr Expr


-- | Definition of a program
data Program = Prog {
  -- Module name and file
  module_name :: String,
  filepath :: FilePath,

  -- A list of modules to import
  -- A module is named by the name of the file, with the first letter an upper case
  imports :: [String],

  -- A list of type definitions
  typedefs :: [Typedef],
 
  -- The body of the module, can be interpreted as the main function
  body :: [Declaration],

  -- Optional interface
  interface :: Maybe Interface
}


-- | Definition of an interface 'file'
-- The list of type declarations must be a subset
-- of the global variables of the implementation
type Interface = [(String, Type)]


instance Eq Program where
  (==) p1 p2 = module_name p1 == module_name p2



-- | Definition of types
data Type =
-- STLC types
    TVar String               -- a
  | TQualified String String  -- qualified type
  | TArrow Type Type          -- A -> B

-- Tensor types
  | TUnit                     -- T
  | TTensor [Type]            -- A1 * .. * An

-- Flavour : duplicable flag
  | TBang Type                 -- !A

-- Quantum related types
  | TQBit                     -- qbit
  | TCirc Type Type           -- circ (A, B)

-- Sum types : bool and generic type instanciation
  | TApp Type Type            -- T a
  | TBool                     -- bool
  | TInt                      -- int

-- Unrelated
  | TLocated Type Extent      -- A @ ex
  deriving Show


-- | This function should be called every time a banged type is produced, since
-- it ensures that no duplicate bangs is added
bang :: Type -> Type
bang (TLocated a ex) =
  TLocated (bang a) ex

bang (TBang a) =
  TBang a

bang a =
  TBang a


-- | Eq instance declaration of types. This instance can't be otained by deriving Eq, because of the
-- TLocated terms : should T and U be equal, then T @ ex and U @ ex' must be equal too.
instance Eq Type where
  (==) (TLocated t1 _) t2 = t1 == t2
  (==) t1 (TLocated t2 _) = t1 == t2
  (==) (TVar x) (TVar y) = x == y
  (==) (TQualified m x) (TQualified m' x') = m == m' && x == x'
  (==) TUnit TUnit = True
  (==) TBool TBool = True
  (==) TInt TInt = True
  (==) TQBit TQBit = True
  (==) (TCirc t1 t2) (TCirc t1' t2') = (t1 == t1') && (t2 == t2')
  (==) (TTensor tlist) (TTensor tlist') = (tlist == tlist')
  (==) (TArrow t1 t2) (TArrow t1' t2') = (t1 == t1') && (t2 == t2')
  (==) (TBang t1) (TBang t2) = (t1 == t2)
  (==) _ _ = False


-- | Types can contain location information, so Type is instance of Located
instance Located Type where
  -- Add location information to a type
  locate (TLocated t ex) _ = TLocated t ex
  locate t ex = TLocated t ex

  -- Return, if any, the location of the type
  location (TLocated _ ex) = Just ex
  location _ = Nothing

  -- Same as locate, with an optional argument
  locate_opt t Nothing = t
  locate_opt t (Just ex) = locate t ex

  -- Recursively removes the location annotations
  clear_location (TLocated t _) = clear_location t
  clear_location (TCirc t u) = TCirc (clear_location t) (clear_location u)
  clear_location (TTensor tlist) = TTensor $ List.map clear_location tlist
  clear_location (TArrow t u) = TArrow (clear_location t) (clear_location u)
  clear_location (TBang t) = TBang (clear_location t)
  clear_location t = t



-- | Definition of patterns
-- Note : - the tuples are required to have a size >= 2. This much is enforced by the parsing grammar,
-- the program must be cautious not to change it
--        - should PUnit be written as PTuple [] ?
data Pattern =
    PUnit                                -- <>
  | PVar String                          -- x
  | PTuple [Pattern]                     -- <x1, .., xn>
  | PDatacon Datacon (Maybe Pattern)     -- datacon (p)
  | PConstraint Pattern Type             -- (x : A)
  | PLocated Pattern Extent              -- x @ ex
  deriving Show


-- | Patterns can contain location information, so Pattern is instance of Located
instance Located Pattern where
  -- Add location information to a pattern
  locate (PLocated p ex) _ = PLocated p ex
  locate p ex = PLocated p ex

  -- Return, if any defined, the location of the pattern
  location (PLocated _ ex) = Just ex
  location _ = Nothing

  -- Same as locate, with an optional argument
  locate_opt p Nothing = p
  locate_opt p (Just ex) = locate p ex

  -- Recursively removes all location annotations
  clear_location (PLocated p _) = clear_location p
  clear_location (PTuple plist) = PTuple $ List.map clear_location plist
  clear_location (PConstraint p t) = PConstraint (clear_location p) t
  clear_location p = p


-- | Definition of a recursive flag, used in the expression ELet to indicate
-- whether the function is recursive or not
data RecFlag = Nonrecursive | Recursive
  deriving (Show, Eq)


-- | Definition of terms
-- Similarly to patterns, tuples have size >= 2, enforced by the grammar
data Expr =
-- STLC
    EVar String                    -- x
  | EQualified String String       -- M.x
  | EFun Pattern Expr              -- fun p -> e
  | EApp Expr Expr                 -- e f

-- Addition of tensors
  | ETuple [Expr]                  -- <e1, .., en>
  | ELet RecFlag Pattern Expr Expr -- let [rec] p = e in f
  | EUnit                          -- <>

-- Addition of sum types
  | EDatacon String (Maybe Expr)   -- datacon e
  | EMatch Expr [(Pattern, Expr)]  -- match e with (x1 -> f1 | x2 -> f2 | ... | xn -> fn)
  | EIf Expr Expr Expr             -- if e then f else g
  | EBool Bool                     -- true / false
  | EInt Int                       -- integer

-- Circuit construction
  | EBox Type                      -- box[A]
  | EUnbox                         -- unbox
  | ERev                           -- rev

-- Unrelated
  | EConstraint Expr Type          -- (e : A)
  | EBuiltin String                -- #builtin s
  | ELocated Expr Extent           -- e @ ex
  deriving Show



-- | Expressions can contain location information, so Expr is instance of Located
instance Located Expr where
  -- Add some location information to an expression
  locate (ELocated e ex) _ = ELocated e ex
  locate e ex = ELocated e ex

  -- Return, if any given, the location of an expression
  location (ELocated _ ex) = Just ex
  location _ = Nothing

  -- Same as locate, with an optional argument
  locate_opt e Nothing = e
  locate_opt e (Just ex) = locate e ex

  -- Recursively removes all location annotations
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



-- | Translate an pattern into the corresponding expression. For example, the pattern <x, y> is transformed
-- into the expression <x, y> (...). The location annotations are conserved.
expr_of_pattern :: Pattern -> Expr
expr_of_pattern PUnit = EUnit
expr_of_pattern (PVar x) = EVar x
expr_of_pattern (PTuple plist) = ETuple $ List.map expr_of_pattern plist
expr_of_pattern (PLocated p ex) = ELocated (expr_of_pattern p) ex


-- | Function reverse of expre_of_pattern : translate an expression into the corresponding pattern. When
-- expr_of_pattern was sure to succeed, this one may fail if called on smth "not a pattern" : for example
-- a lambda abstraction. The locations are conserved.
pattern_of_expr :: Expr -> Pattern
pattern_of_expr EUnit = PUnit
pattern_of_expr (EVar x) = PVar x
pattern_of_expr (ETuple elist) = PTuple $ List.map pattern_of_expr elist
pattern_of_expr (ELocated e ex) = PLocated (pattern_of_expr e) ex



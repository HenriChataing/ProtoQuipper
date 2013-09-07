-- | This module defines the /surface syntax/ of types, patterns, and
-- expressions, as parsed by the parser. This should not be confused
-- with the /internal syntax/ defined in "Typing.CoreSyntax", which is
-- used internally by the interpreter and type checker.
module Parsing.Syntax where

import Classes

import Parsing.Location
import Monad.QuipperError

import Control.Exception
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
    PWildcard                               -- ^ The \"wildcard\" pattern: \"@_@\". This pattern matches any value, and the value is to be discarded.
                                         -- In Proto-Quipper, a wildcard can only match a duplicable value. 
  | PUnit                                -- ^ Unit pattern: @()@.
  | PBool Bool                           -- ^ Boolean pattern: @true@ or @false@.
  | PInt Int                             -- ^ Integer pattern.
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

-- | An applicative pattern, such as /f/ /x/ /y/, consists of an
-- identifier and one or more arguments. Such patterns are appropriate
-- for \"let rec\", and are also permitted for non-recursive \"let\".
type AppPattern = (Pattern, [Pattern])

-- | Check whether a pattern is a single identifier (possibly located),
-- and therefore appropriate as the head of an applicative pattern.
isPVar :: Pattern -> Bool
isPVar (PVar x) = True
isPVar (PLocated p ex) = isPVar p
isPVar _ = False

-- | Check whether a pattern is a single data constructor (possibly
-- located), and therefore appropriate as the head of a data
-- constructor pattern. If yes, return the data constructor; if no,
-- return 'Nothing'.
isPDatacon :: Pattern -> Maybe Datacon
isPDatacon (PDatacon d Nothing) = Just d
isPDatacon (PLocated p ex) = isPDatacon p
isPDataon _ = Nothing

-- | A \"general pattern\" is either a simple pattern (such as 
-- (/x/, /y/) or /h/:/t/), or an applicative pattern.
data GenPattern =
    SimplePattern Pattern  -- ^ A simple pattern.
  | AppPattern AppPattern  -- ^ An applicative pattern.
    deriving (Show)

-- | Translate an expression to the corresponding pattern, which may
-- be a simple or applicative pattern.  If the input expression is not
-- a pattern, for example, a lambda abstraction, then return 'Nothing'
-- 
-- Because LR parsers have limited look-ahead, we initially parse a
-- pattern as an expression, but then immediately convert it to a
-- pattern. Parsing patterns as expressions has the added benefit that
-- patterns can make use of data constructors and infix operators. For
-- example, the following is a legal definition of a binary operator
-- \"+\":
-- 
-- > let Pair (x, y) + Pair (x', y') = Pair (x+x', y+y');;
maybe_gen_pattern_of_expr :: Expr -> Maybe GenPattern
maybe_gen_pattern_of_expr (EVar x) = do
  return (SimplePattern (PVar x))
maybe_gen_pattern_of_expr (ETuple elist) = do
  plist <- mapM maybe_pattern_of_expr elist
  return (SimplePattern (PTuple plist))
maybe_gen_pattern_of_expr EUnit = do
  return (SimplePattern PUnit)
maybe_gen_pattern_of_expr (EDatacon d Nothing) = do
  return (SimplePattern (PDatacon d Nothing))
maybe_gen_pattern_of_expr (EDatacon d (Just e)) = do
  p <- maybe_pattern_of_expr e
  return (SimplePattern (PDatacon d (Just p)))
maybe_gen_pattern_of_expr (EBool b) = do
  return (SimplePattern (PBool b))
maybe_gen_pattern_of_expr (EInt n) = do
  return (SimplePattern (PInt n))
maybe_gen_pattern_of_expr (ELocated e ex) = do
  p <- maybe_gen_pattern_of_expr e
  case p of
    SimplePattern sp ->
      return (SimplePattern (PLocated sp ex))
    AppPattern ap ->
      -- we cannot locate an applicative pattern
      return (AppPattern ap)
maybe_gen_pattern_of_expr (EApp e1 e2) = do
  p1 <- maybe_gen_pattern_of_expr e1
  p2 <- maybe_pattern_of_expr e2
  case p1 of
    SimplePattern sp -> 
      -- This could be an applicative pattern f x or a data
      -- constructor pattern Con x, depending on whether the head is a
      -- variable or a data constructor.
      if isPVar sp then do
        return (AppPattern (sp, [p2]))
      else case isPDatacon sp of
        Just d -> do
          return (SimplePattern (PDatacon d (Just p2)))
        Nothing -> do         
          Nothing
    AppPattern (x, ps) -> do
      return (AppPattern (x, ps ++ [p2]))
maybe_gen_pattern_of_expr _ = Nothing

-- | Like 'maybe_gen_pattern_of_expr', but only accept simple patterns.
maybe_pattern_of_expr :: Expr -> Maybe Pattern
maybe_pattern_of_expr e = do
  p <- maybe_gen_pattern_of_expr e
  case p of
    SimplePattern sp -> return sp
    _ -> Nothing

-- | Translate an expression to a functional pattern, or return
-- 'Nothing' if the expression is not a valid functional pattern.
maybe_app_pattern_of_expr :: Expr -> Maybe AppPattern
maybe_app_pattern_of_expr e = do
  p <- maybe_gen_pattern_of_expr e
  case p of
    AppPattern ap -> return ap
    _ -> Nothing

-- | Like 'maybe_gen_pattern_of_expr', but in case of an invalid
-- pattern, trow a 'ParsingOtherError' with text \"bad pattern\".
gen_pattern_of_expr :: Expr -> GenPattern
gen_pattern_of_expr e =
  case maybe_gen_pattern_of_expr e of
    Just p -> p
    Nothing ->
      throw $ locate_opt (ParsingOtherError "bad pattern") (location e)

-- | Like 'maybe_pattern_of_expr', but in case of an invalid simple
-- pattern, trow a 'ParsingOtherError' with text \"bad pattern\".
pattern_of_expr :: Expr -> Pattern
pattern_of_expr e = 
  case maybe_pattern_of_expr e of
    Just p -> p
    Nothing ->
      throw $ locate_opt (ParsingOtherError "bad pattern") (location e)

-- | Like 'maybe_app_pattern_of_expr', but in case of an invalid
-- functional pattern, trow a 'ParsingOtherError' with text \"bad
-- pattern\".
app_pattern_of_expr :: Expr -> AppPattern
app_pattern_of_expr e = 
  case maybe_app_pattern_of_expr e of
    Just p -> p
    Nothing ->
      throw $ locate_opt (ParsingOtherError "bad pattern") (location e)

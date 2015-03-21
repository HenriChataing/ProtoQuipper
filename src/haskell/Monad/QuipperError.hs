{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}


-- | This module provides a type enumerating the errors that can be thrown by the lexer, parser, type inference algorithm, interpreter or compiler.
-- These errors will be divided between these categories.
module Monad.QuipperError where

import Prelude hiding (print)

import Parsing.Location

import qualified Control.Exception as E
import Data.Typeable

import Data.List as List


-- | The class of ProtoQuipper exceptions.
class Show a => QError a where
  prefix :: a -> String                       -- ^ The prefix of all error messages. For example: \"Parsing error\".
  printE :: a -> Extent -> String             -- ^ Display the error, with the additionnal extent information.

  printE err ext =
    if ext == extent_unknown then
      prefix err ++ ": " ++ show err
    else
      prefix err ++ ":" ++ show ext ++ ": " ++ show err


-- | A type that covers all quipper errors.
data QuipperError =
  QuipperError String
  deriving (Typeable)


instance Show QuipperError where
  show (QuipperError msg) = msg

instance E.Exception QuipperError



------------------------------------------
-- ** Methods for throwing exceptions.


-- | A general method to throw quipper errors.
throw :: QError a => a      -- ^ An error.
      -> Maybe Extent       -- ^ An optional extent.
      -> b
throw err ext =
  case ext of
    Nothing ->
        E.throw $ QuipperError $ printE err extent_unknown
    Just ext ->
        E.throw $ QuipperError $ printE err ext


-- | Throw an error whose extent is unknown (NE stands for \"No Extent\").
throwNE :: QError a => a
        -> b
throwNE err =
  throw err Nothing


-- | Throw an error whose extent is known (WE stands for \"With Extent\").
throwWE :: QError a => a
        -> Extent
        -> b
throwWE err ext =
  throw err $ Just ext


------------------------------------------
-- ** Definition of common errors.


-- | Enumeration of file errors. It contains all the errors thrown before the parsing of files.
data FileError =
    NonExistentModule String                                                              -- ^ Thrown when the program can't find the implementation of a module.
  | DuplicateImplementation String String String                                          -- ^ Thrown if two implementation files of the same module are found.
  | CircularDependency String [String]                                                    -- ^ Thrown in case of circular dependencies.
  deriving (Typeable)


instance QError FileError where
  prefix _ = "File error"


instance Show FileError where
  show (NonExistentModule mod) =
    "couldn't find the implementation of the module " ++ mod

  show (DuplicateImplementation mod p1 p2) =
    "several existing implementations of the module " ++ mod ++ " have been found:\n" ++
    "    at: " ++ p1 ++ "\n" ++
    "    at: " ++ p2

  show (CircularDependency mod includes) =
    "circular module dependency:\n" ++
    "    the module " ++ mod ++ " imports " ++ List.head includes ++
    List.foldl (\rec m ->
          rec ++ "\n    which imports " ++ m) "" (List.tail includes)



-- | Enumeration of lexing errors.
data LexicalError =
    LexicalError String                                                                   -- ^ Lexical error, thrown when an unknown token is read.
  deriving (Typeable)


instance QError LexicalError where
  prefix _ = "Lexical error"


instance Show LexicalError where
  show (LexicalError msg) =
    "unknown token " ++ msg



-- | Enumeration of parsing and syntax errors.
data SyntaxError =
    ParsingError String                                                                   -- ^ Parsing error, the argument is the token on which the error occurred.
  | ParsingOtherError String                                                              -- ^ Other parsing error (e.g., bad pattern).
  | EndOfFileError                                                                        -- ^ Thrown when the parser arrived at the end of a file with an incomplete expression.
  | WrongTypeArguments String Int Int                                                     -- ^ An algebraic type has been used with a wrong number of arguments. The first
                                                                                          -- argument is the name of the type, the two next the actual and expected number of
                                                                                          -- arguments.
  | BadBoxType String                                                                     -- ^ Box constructor called with something not a quantum data type.
  | UnboundVariable String                                                                -- ^ Variable not in scope. The arguments are name and location of the variable.
  | UnboundDatacon String                                                                 -- ^ Data constructor not in scope. The arguments are name and location of the constructor.
  | UndefinedType String                                                                  -- ^ Type definition not in scope. The arguments are name and location of the constructor.
  | UndefinedBuiltin String                                                               -- ^ As the name indicates, the program tried to used an undefined built-in operation.
  | UnboundModule String                                                                  -- ^ When a reference to an undefined module is used.
  deriving (Typeable)


instance QError SyntaxError where
  prefix _ = "Syntax error"


instance Show SyntaxError where
  show (ParsingError tk) =
    "on token " ++ tk

  show (ParsingOtherError tk) =
    tk

  show EndOfFileError =
    "unexpected end of file"

  show (WrongTypeArguments typ exp act) =
    if exp == 0 then     "the type '" ++ typ ++ "' expects no arguments, but has been given " ++ show act
    else                 "the type '" ++ typ ++ "' expects " ++ show exp ++ " arguments, but has been given " ++ show act

  show (BadBoxType typ) =
    "in a box constructor: the type '" ++ typ ++ "' is not quantum"

  show (UnboundVariable x) =
    "unbound variable " ++ x

  show (UnboundDatacon dcon) =
    "unbound data constructor " ++ dcon

  show (UndefinedType typ) =
    "undefined type " ++ typ

  show (UndefinedBuiltin s) =
    "undefined builtin operator " ++ s

  show (UnboundModule m) =
    "unbound module " ++ m


-- | Enumeration of the run-time errors. Most don't make sense as they can be detected as soon as the type inference.
data RuntimeError =
    NotBoolError String                                                                   -- ^ A value not of type @bool@ was used in a conditional.
  | NoMatchError String                                                                   -- ^ Non exhaustive pattern matching.
  | NotFunctionError String                                                               -- ^ A value not a function has been applied to an argument.
  | MatchingError String String                                                           -- ^ When a pattern and a value from a binding (@let@, @fun@, @match@) are found to have
                                                                                          -- non-matching structures.
  | BuiltinError String String                                                            -- ^ A built-in operation is applied to a value of the wrong type. The first argument is the name
                                                                                          -- of the built-in operator, and the second is what was expected, e.g. \"an integer\".
  | WrongDataArguments String                                                             -- ^ Thrown when a data constructor expecting no arguments is given one.
  | UserError String                                                                      -- ^ User errors, thrown at run-time by the user using the appropriate built-in operation.
  deriving (Typeable)


instance QError RuntimeError where
  prefix _ = "Runtime error"


instance Show RuntimeError where
  show (NotBoolError v) =
    v ++ " is not of type bool"

  show (NoMatchError v) =
    "this pattern matching is not exhaustive: the value " ++ v ++ " is not matched"

  show (NotFunctionError v) =
    v ++ " is not a function"

  show (MatchingError p q) =
    "can't bind the objects " ++ p ++ " and " ++ q

  show (BuiltinError p q) =
    "built-in " ++ p ++ " applied to something that is not " ++ q

  show (WrongDataArguments dcon) =
    "the data constructor " ++ dcon ++ " expects no arguments, but has been given one"

  show (UserError msg) =
    msg


-- | Enumeration of all typing errors.
data TypingError =
    TypingError String String                                                             -- ^ Typing error, but missing detailed information. The goal is to have as few of them as possible.

  | DetailedTypingError String String (Maybe String) String                               -- ^ Typing error: the two first arguments are the types that couldn't be matched (the first the actual type,
                                                                                          -- the other one the expected type), the next string locates the actual type inside of a larger one, the
                                                                                          -- last string is the expression cause of the typing error, and the rest is the location.

  | NonDuplicableError String (Maybe String)                                              -- ^ A non duplicable term (e.g., of type qubit), has been used in a non linear fashion. The string
                                                                                          -- argument is the expression cause of all this (used in a non linear fashion), the rest the
                                                                                          -- location of the expression.

  | InfiniteTypeError String [String] (Maybe String) String                               -- ^ Trying to build an infinite type. The first string is the type variable cause of the error,
                                                                                          -- the list is the sequence of type constraints which caused the error. The optional string
                                                                                          -- locate the variable inside of a larger type, and the last string is the expression in which the error
                                                                                          -- occurred, the rest is location information.
  deriving (Typeable)


instance QError TypingError where
  prefix _ = "Typing error"


instance Show TypingError where
  show (TypingError ta tb) =
    "cannot unify the type \"" ++ ta ++ "\" with the type \"" ++ tb ++ "\""

  show (DetailedTypingError ta tb mt e) | ta == tb = "type error"
                                        | otherwise =
    "\n    couldn't match actual type\n" ++
    ta ++ "\n" ++
    "    with expected type\n" ++
    tb ++ "\n" ++
    (case mt of
       Just typ ->
           "    In the type\n" ++
           typ ++ "\n"
       Nothing ->
           "") ++
    "    In the type of\n" ++
    e

  show (NonDuplicableError e _) =
    "the term " ++ e ++ " is not duplicable"

  show (InfiniteTypeError t clist mt e) =
    "\n    couldn't build the infinite type\n" ++
    t ++ "\n" ++ List.concat (List.map (\c -> c ++ "\n") clist) ++
    (case mt of
       Just typ ->
           "    In the type\n" ++
           typ ++ "\n"
       Nothing ->
           "") ++
    "    In the type of\n" ++
    e



-- | The errors originating from programming errors.
data ProgramError =
    ProgramError String                                                                   -- ^ Programming errors, thrown on unexpected behaviours.
  deriving (Typeable)


instance QError ProgramError where
  prefix _ = "PROGRAM ERROR"


instance Show ProgramError where
  show (ProgramError msg) =
    msg



-- | Definition of some warnings. If the option \'Wall\' is given, warnings will indeed be turned into errors.
data Warning =
    UnexhaustiveMatch [String]                                                            -- ^ Unexhaustive pattern matching. The argument lists some cases that are not matched.
  | FailedMatch                                                                           -- ^ A pattern matching always fails: e.g. @let Nil = x:xs in ...@
  | AmbiguousUnbox                                                                        -- ^ Could not resolve the call type of an unbox operator.
  | NakedExpressionToplevel                                                               -- ^ At compile time, a naked expression was found at top-level.
  deriving (Typeable)


instance QError Warning where
  prefix _ = "WARNING"


instance Show Warning where
  show (UnexhaustiveMatch []) =
    "this pattern matching is not exhaustive"
  show (UnexhaustiveMatch [c]) =
    "this pattern matching is not exhaustive:\n" ++
    "    the case\n" ++
    c ++ "\n" ++
    "    is not matched"
  show (UnexhaustiveMatch cases) =
    "this pattern matching is not exhaustive:\n" ++
    "    the cases\n" ++
    List.foldl (\s c -> s ++ c ++ "\n") "" cases ++
    "    are not matched"

  show FailedMatch =
    "this pattern matching will always fail"

  show AmbiguousUnbox =
    "couldn't solve the instance for this unbox operator"

  show NakedExpressionToplevel =
    "naked expression at toplevel"

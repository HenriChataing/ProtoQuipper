{-# LANGUAGE DeriveDataTypeable #-}

-- | This module provides a data type sampling the errors thrown during the execution of the program,
--  from the lexing, parsing, to the type inference and interpretation of the code.
module Monad.QuipperError where

import Parsing.Localizing

import Control.Exception
import Data.Typeable

import Data.List as List


-- | Data type of the program exceptions.
data QError =

-- FILE ERRORS

    NotExistingModule String                                                              -- ^ Thrown when the program can't find the implementation of a module.
  | DuplicateImplementation String String String                                          -- ^ Thrown if two implementation files of the same module are found.
  | CyclicDependencies String [String]                                                    -- ^ Thrown when it is found that the module dependencies form a cycle.

-- LEXICAL ERRORS
    
  | LexicalError (String, Extent)                                                         -- ^ Lexical error, thrown when an unknown token is read.

-- SYNTAX ERRORS

  | ParsingError String                                                                   -- ^ Parsing error, the argument is the token on which the error occured.
  | ErrorEndOfFile                                                                        -- ^ Thrown when the parser arrived at the end of a file with an incomplete expression.
  | WrongTypeArguments String Int Int (String, Extent)                                    -- ^ An algebraic type has been called with a wrong number of arguments. The first
                                                                                          -- argument is the name of the type, the two next the actual and expected number of
                                                                                          -- arguments. The rest gives the location of the error.

  | BoxTypeError String (String, Extent)                                                  -- ^ Box constructor called with something not a quantum data type.
  | UnboundVariable String (String, Extent)                                               -- ^ Variable not in scope. The arguments are name and location of the variable.
  | UnboundDatacon String (String, Extent)                                                -- ^ Data constructor not in scope. The arguments are name and location of the constructor.

  | UndefinedBuiltin String (String, Extent)                                              -- ^ As the name indicates, the program tried to used an undefined builtin, of name 
                                                                                          -- the first argument, at the location the second.

-- RUN TIME ERRORS

  | NotBoolError String (String, Extent)                                                  -- ^ During execution, something not a boolean has been used as an if condition.
  | NoMatchError String (String, Extent)                                                  -- ^ During execution, non exhaustive pattern matching.
  | NotFunctionError String (String, Extent)                                              -- ^ During execution, something not a function has been applied to an argument.
  | MatchingError String String                                                           -- ^ During execution, a pattern and a value from a binding (let, fun, match) are found to have
                                                                                          -- unmatching structures.
 
-- TYPING ERRORS

  | TypingError String String                                                             -- ^ Typing error, but missing detailed information. The goal is to have as few of them as possible.

  | DetailedTypingError String String (Maybe String) String (String, Extent)              -- ^ Typing error : the two first arguments are the types that couldn't be matched (the first the actual type, 
                                                                                          -- the other one the expected type), the next string locates the actual type inside of a larger one, the
                                                                                          -- last string is the expression cause of the typing error, and the rest is the location.

  | NonDuplicableError String (String, Extent)                                            -- ^ A non duplicable term (eg of type qbit), has been used in a non linear fashion. The string
                                                                                          -- argument is the expression cause of all this (used in a non linear fashion), the rest the
                                                                                          -- location of the expression.

  | InfiniteTypeError String [String] (Maybe String) String (String, Extent)              -- ^ Trying to build an infinite type. The first string is the type variable cause of the error,
                                                                                          -- the list is the sequence of type constraints which caused the error. The optional string
                                                                                          -- locate the variable inside of a larger type, and the last string is the expression in which the error
                                                                                          -- occured, the rest is location information.

  | WrongDataArguments String (String, Extent)                                            -- ^ Thrown when a data constructor expecting no arguments is given one.

-- MISC

  | MiscError String                                                                      -- ^ Misc errors. The argument is an error message.
  | ProgramError String                                                                   -- ^ Grave : programming errors, thrown when something that shouldn't have happened did.
  deriving (Typeable)


-- | Error pretty printing
instance Show QError where
  show (NotExistingModule mod) =
    "Error: couldn't find the implementation of the module " ++ mod

  show (DuplicateImplementation mod p1 p2) =
    "Error: several existing implementations of the module " ++ mod ++ " have been found:\n" ++
    "   at: " ++ p1 ++ "\n" ++
    "   at: " ++ p2 

  show (CyclicDependencies mod includes) =
    "Error: the module dependencies form a cycle:\n" ++
    "In the module " ++ mod ++
    List.foldl (\rec m ->
                  rec ++ "\n  which imports " ++ m) "" includes

  show (LexicalError (f, ex)) =
    f ++ ":" ++ show ex ++ ": unknown token"

  show (ParsingError tk) =
    "Parsing error: on token " ++ tk
  show ErrorEndOfFile =
    "Parsing error: unexpected end of file"

  show (WrongTypeArguments typ exp act (f, ex)) =
    f ++ ":" ++ show ex ++
    if exp == 0 then     ": the type " ++ typ ++ " expects no arguments, but has been given " ++ show act
    else                 ": the type " ++ typ ++ " expects " ++ show exp ++ " arguments, but has been given " ++ show act

  show (BoxTypeError typ (f, ex)) =
    f ++ ":" ++ show ex ++ ": the box constructor, which expects a quantum data type as argument,  has been called on " ++ typ

  show (UnboundVariable x (f, ex)) =
    f ++ ":" ++ show ex ++ ": unbound variable " ++ x

  show (UnboundDatacon dcon (f, ex)) =
    f ++ ":" ++ show ex ++ ": unbound data constructor " ++ dcon

  show (UndefinedBuiltin s (f, ex)) =
    f ++ ":" ++ show ex ++ ": undefined builtin value " ++ s

  show (NotBoolError v (f, ex)) =
    f ++ ":" ++ show ex ++ ": " ++ v ++ " is not of type bool"

  show (NoMatchError v (f, ex)) =
    f ++ ":" ++ show ex ++ ": this pattern matching is not exhaustive: the value " ++ v ++ " is not matched"

  show (NotFunctionError v (f, ex)) =
    f ++ ":" ++ show ex ++ ": " ++ v ++ " is not a function"
  
  show (MatchingError p q) =
    "Error: can't bind the objects " ++ p ++ " and " ++ q

  show (TypingError ta tb) =
    "Typing error: cannot unify the type \"" ++ ta ++ "\" with the type \"" ++ tb ++ "\""

  show (DetailedTypingError ta tb mt e (f, ex)) =
    f ++ ":" ++ show ex ++":\n" ++
    "    Couldn't match actual type\n" ++
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

  show (NonDuplicableError e (f, ex)) =
    f ++ ":" ++ show ex ++ ": the term " ++ e ++ " is not duplicable"

  show (InfiniteTypeError t clist mt e (f, ex)) =
    f ++ ":" ++ show ex ++ ":\n" ++
    "    Couldn't build the infinite type\n" ++
    t ++ "\n" ++ List.concat (List.map (\c -> c ++ "\n") clist) ++
    (case mt of
       Just typ ->
           "    In the type\n" ++
           typ ++ "\n"
       Nothing ->
           "") ++
    "    In the type of\n" ++
    e

  show (WrongDataArguments dcon (f, ex)) =
    f ++ ":" ++ show ex ++ ": the data constructor " ++ dcon ++ " expects no arguments, but has been given one"

  show (MiscError msg) = "Error: " ++ msg
  show (ProgramError msg) = "IMPORTANT: PROGRAM ERROR: " ++ msg


-- | The type QError must be declared as an exception to be thrown/caught in the IO monad.
instance Exception QError

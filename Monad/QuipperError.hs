{-# LANGUAGE DeriveDataTypeable #-}

-- | This module provides a data type sampling the errors thrown during the execution of the program,
--  from the lexing, parsing, to the type inference and interpretation of the code
module Monad.QuipperError where

import Parsing.Localizing

import Control.Exception
import Data.Typeable

import Data.List as List

data QError =

-- FILE ERRORS

    -- Related to module implementations
    NotExistingModule String
  | DuplicateImplementation String String String
    -- Cyclic dependencies in modules
  | CyclicDependencies String

-- LEXICAL ERRORS
    
    -- Lexical, thrown by the lexer when coming upon an unkown token
  | LexicalError (String, Extent)

-- SYNTAX ERRORS

    -- Parsing error : a same kind of error is used to describe all syntax errors
  | ParsingError String
    -- Parsing error : unexpected end of file
  | ErrorEndOfFile
    -- A type constructor expect a certain number of arguments n, and is given m /= n instead
  | WrongTypeArguments String Int Int (String, Extent)
    -- The box constructor requires a quantum data type, this error is thrown otherwise
  | BoxTypeError (String, Extent)
    -- Variable / datacon / builtin is unbound / undefined
  | UnboundVariable String (String, Extent)
  | UnboundDatacon String (String, Extent)
  | UndefinedBuiltin String (String, Extent)


-- RUN TIME ERRORS

    -- The condition of a if .. then .. else is not a boolean
  | NotBoolError String (String, Extent)
    -- No match found for a value in a match .. with .. construction
  | NoMatchError String (String, Extent)
    -- The object is not a function
  | NotFunctionError String (String, Extent)
    -- Matching errors
  | MatchingError String String
 
-- TYPING ERRORS

  | TypingError String String                                                             -- ^ Typing error, but missing detailed information. The goal is to have as few of them as possible.
  | DetailedTypingError String String (Maybe String) String (String, Extent)              -- ^ Typing error : actual type .. vs expected type .. in the type .. in type of .. at extent ..
  | NonDuplicableError String (String, Extent)                                            -- ^ A non duplicable term (eg of type qbit), has been used in a non linear fashion
  | InfiniteTypeError String [String] (Maybe String) String (String, Extent)              -- ^ Trying to build an infinite type

-- MISC

    -- Other errors
  | MiscError String
    -- Program errors
  | ProgramError String
  deriving (Typeable)


-- | Error pretty printing
instance Show QError where
  show (NotExistingModule mod) = "Error: the module " ++ mod ++ " lacks an implementation"
  show (DuplicateImplementation mod p1 p2) = "Error: several implementations of the module " ++ mod ++ " have been found:\n" ++
                                             "   at: " ++ p1 ++ "\n" ++
                                             "   at: " ++ p2 
  show (CyclicDependencies mod) = "Error: cyclic dependency in module " ++ mod

  show (LexicalError (f, ex)) = f ++ ":" ++ show ex ++ ": unknown token"

  show (ParsingError tk) = "Parsing error: on token " ++ tk
  show ErrorEndOfFile = "Error: unexpected end of file"
  show (WrongTypeArguments typ exp act (f, ex)) =
    f ++ ":" ++ show ex ++
    if exp == 0 then     ": the type " ++ typ ++ " expects no arguments, but has been given " ++ show act
    else                 ": the type " ++ typ ++ " expects " ++ show exp ++ " arguments, but has been given " ++ show act 
  show (BoxTypeError (f, ex)) = f ++ ":" ++ show ex ++ ": the box constructor expect a quantum data type as argument"
  show (UnboundVariable x (f, ex)) = f ++ ":" ++ show ex ++ ": unbound variable " ++ x
  show (UnboundDatacon dcon (f, ex)) = f ++ ":" ++ show ex ++ ": unbound data constructor " ++ dcon
  show (UndefinedBuiltin s (f, ex)) = f ++ ":" ++ show ex ++ ": undefined builtin value " ++ s

  show (NotBoolError v (f, ex)) = f ++ ":" ++ show ex ++ ": " ++ v ++ " is not of type bool"
  show (NoMatchError v (f, ex)) = f ++ ":" ++ show ex ++ ": this pattern matching is not exhaustive: the value " ++ v ++ " is not matched"
  show (NotFunctionError v (f, ex)) = f ++ ":" ++ show ex ++ ": " ++ v ++ " is not a function"
  show (MatchingError p q) = "Error: can't bind the objects " ++ p ++ " and " ++ q

  show (TypingError ta tb) = "Typing error: cannot unify the type \"" ++ ta ++ "\" with the type \"" ++ tb ++ "\""

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

  show (NonDuplicableError e (f, ex)) = f ++ ":" ++ show ex ++ ": the term " ++ e ++ " is not duplicable"
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

  show (MiscError msg) = "Error: " ++ msg
  show (ProgramError msg) = "IMPORTANT: PROGRAM ERROR: " ++ msg


-- | The type QError must be declared as an exception to be thrown/caught in the IO monad
instance Exception QError

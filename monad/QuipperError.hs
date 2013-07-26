{-
   This module provides a data type sampling the errors thrown during the execution of the program,
  from the lexing, parsing, to the type inference and interpretation of the code
-}

module QuipperError where

import Localizing

import Control.Exception
import Data.Typeable

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

    -- Typing errors : thrown during the unification 
  | TypingError String String                                       -- Typing error
  | DetailedTypingError String String String (String, Extent)       -- Typing error : actual vs expected in type of expr at extent ex
    -- A non duplicable term (eg of type qbit), has been used in a non linear fashion
  | NonDuplicableError String (String, Extent)

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
  show (DetailedTypingError ta tb e (f, ex)) = f ++ ":" ++ show ex ++": couldn't match actual type\n" ++
                                          "    " ++ ta ++ "\n" ++
                                          "with expected type\n" ++
                                          "    " ++ tb ++ "\n" ++
                                          "in the type of\n" ++
                                          "    " ++ e
  show (NonDuplicableError e (f, ex)) = f ++ ":" ++ show ex ++ ": the term " ++ e ++ " is not duplicable"

  show (MiscError msg) = "Error: " ++ msg
  show (ProgramError msg) = "IMPORTANT: PROGRAM ERROR: " ++ msg


-- | The type QError must be declared as an exception to be thrown/caught in the IO monad
instance Exception QError

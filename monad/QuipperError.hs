{-
   This module provides a data type sampling the errors thrown during the execution of the program,
  from the lexing, parsing, to the type inference and interpretation of the code
-}

module QuipperError where

import Localizing

import Control.Exception
import Data.Typeable

data QError =
    
    -- Lexical, thrown by the lexer when coming upon an unkown token
    LexicalError Extent

    -- Parsing error : a same kind of error is used to describe all syntax errors
  | ParsingError String

    -- The box constructor requires a quantum data type, this error is thrown otherwise
  | BoxTypeError Extent

  | NoBoxError Extent

    -- Variable / datacon is unbound / undefined
  | UnboundVariable String Extent
  | UnboundDatacon String Extent

    -- A type constructor expect a certain number of arguments n, and is given m /= n instead
  | WrongTypeArguments String Int Int Extent

    -- A non duplicable term (eg of type qbit), has been used in a non linear fashion
  | NonDuplicableError String Extent

    -- Matching errors
  | MatchingError String String

    -- Strictly runtime error : when no match is found in a match .. with .. construction
  | NoMatchError String Extent

    -- Something not a function is applied to an argument
  | NotFunctionError String Extent

    
  | NotUnionError String

    -- Runtime error, if the condition of a if .. then .. else is not a boolean
  | NotBoolError String Extent
 
    -- Typing errors : thrown during the unification 
  | TypingError String String                             -- Typing error
  | DetailedTypingError String String String Extent       -- Typing error : actual vs expected in type of expr at extent ex

    {-
       Everything else
    -}
  | MiscError String

    {- Programming errors -}
  | ProgramError String
  deriving (Typeable)

{-
   Error printing
-}

instance Show QError where
  show (LexicalError ex) = "Lexical error: at extent " ++ show ex
  show (ParsingError tk) = "Parsing error: on token " ++ tk
  show (BoxTypeError ex) = "Parsing error: constructor box expect a quantum data type as argument: at extent " ++ show ex

  show (UnboundVariable x ex) = "Error: unbound variable " ++ x ++ ": at extent " ++ show ex
  show (UnboundDatacon dcon ex) = "Error: unbound data constructor " ++ dcon ++ ": at extent " ++ show ex
  show (WrongTypeArguments typ exp act ex) =
    if exp == 0 then
      "Error: the type " ++ typ ++ " expects no arguments, but has been given " ++ show act ++ ": at extent " ++ show ex
    else
      "Error: the type " ++ typ ++ " expects " ++ show exp ++ " arguments, but has been given " ++ show act ++ ": at extent " ++ show ex

  show (NonDuplicableError e ex) = "Error: the term " ++ e ++ " is not duplicable: at extent " ++ show ex

  show (NoBoxError ex) = "Error: unbox operations must be executed in the context of a box: at extent " ++ show ex
  show (MatchingError p q) = "Error: the objects " ++ p ++ " and " ++ q ++ " don't have the same type"
  show (NoMatchError v ex) = "Error: the pattern matching is not exhaustive: with the value " ++ v ++ ": at the extent " ++ show ex
  show (NotFunctionError v ex) = "Error: " ++ v ++ " is not a function: at extent " ++ show ex
  show (NotUnionError v) = "Error: " ++ v ++ " doesn't have a union type"
  show (NotBoolError v ex) = "Error: " ++ v ++ " is not of type bool: at extent " ++ show ex

  show (TypingError ta tb) = "Typing error: cannot unify the type \"" ++ ta ++ "\" with the type \"" ++ tb ++ "\""
  show (DetailedTypingError ta tb e ex) = "Typing error: couldn't match actual type\n" ++
                                          "    " ++ ta ++ "\n" ++
                                          "with expected type\n" ++
                                          "    " ++ tb ++ "\n" ++
                                          "in the type of\n" ++
                                          "    " ++ e ++ "\n" ++
                                          "at the extent " ++ show ex

  show (MiscError msg) = "Error: " ++ msg
  show (ProgramError msg) = "IMPORTANT: PROGRAM ERROR: " ++ msg

{-
   The type QError must be declared as an exception to be thrown/caught in the IO monad
-}
instance Exception QError

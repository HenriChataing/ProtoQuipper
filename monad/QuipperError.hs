{-
   This module provides a data type sampling the errors thrown during the execution of the program,
  from the lexing, parsing, to the type inference and interpretation of the code
-}

module QuipperError where

import Localizing

import Control.Exception
import Data.Typeable

data QError =
    {-
       Lexical errors, thrown during the lexing of the input file.
       It is of but one type of error : unknown token %%%
       The extent give the location of the error.
    -}
    LexicalError Extent

    {-
       Parsing errors, thrown during the parsing. Parsing errors generally correspond to an unknwon
       sequence of tokens. As of now, only one parsing error is provided to represent them all. Others
       will be added later to differenciate between missing parenthesis, ... -}
  | ParsingError String
  | BoxTypeError Extent

    {-
       Runtime errors. Some of those may overlap with the type inference errors, but the context in which
       they are thrown is different
    -}
  | NoBoxError Extent
  | UnboundVariable String Extent
  | UnboundDatacon String Extent
  | MatchingError String String
  | NoMatchError String Extent
  | NotFunctionError String Extent
  | NotUnionError String
  | NotBoolError String Extent
  
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
  show (NoBoxError ex) = "Error: unbox operations must be executed in the context of a box: at extent " ++ show ex
  show (MatchingError p q) = "Error: the objects " ++ p ++ " and " ++ q ++ " don't have the same type"
  show (NoMatchError v ex) = "Error: the pattern matching is not exhaustive: with the value " ++ v ++ ": at the extent " ++ show ex
  show (NotFunctionError v ex) = "Error: " ++ v ++ " is not a function: at extent " ++ show ex
  show (NotUnionError v) = "Error: " ++ v ++ " doesn't have a union type"
  show (NotBoolError v ex) = "Error: " ++ v ++ " is not of type bool: at extent " ++ show ex

  show (TypingError ta tb) = "Typing error: cannot unify the type \"" ++ ta ++ "\" with the type \"" ++ tb ++ "\""
  show (DetailedTypingError ta tb e ex) = "Typing error: can not match the actual type\n" ++
                                          "    " ++ ta ++ "\n" ++
                                          "with the expected type\n" ++
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

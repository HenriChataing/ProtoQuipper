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
       Type inference errors.
    -}
  | UnboundVariable String Extent

    {-
       Everything else
    -}
  | MiscError String
  deriving (Typeable)

{-
   Error printing
-}

instance Show QError where
  show (LexicalError ex) = "Lexical error: at extent " ++ show ex
  show (ParsingError tk) = "Parsing error: on token " ++ tk
  show (BoxTypeError ex) = "Parsing error: constructor box expect a quantum data type as argument: at extent " ++ show ex
  show (UnboundVariable x ex) = "Error: unbound variable " ++ x ++ ": at extent " ++ show ex
  show (MiscError msg) = "Error: " ++ msg

{-
   The type QError must be declared as an exception to be thrown/caught in the IO monad
-}
instance Exception QError

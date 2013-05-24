module Utils where

import Localizing

import Data.Char as Char
import Data.Map as Map
import Data.List as List

-----------------------------------------
--  Some string manipulation functions --

-- Convert a digit to subscript character
subdigit :: Int -> Char
-----------------------
 -- 8320 is decimal for 2080 -- Subscript digits are \x2080 .. \x2089
subdigit d = toEnum (8320 + d)

-- Subscripts a string
subscript :: String -> String
-----------------------------
subscript = List.map (\c -> if isDigit c then
                              subdigit (digitToInt c)
                            else
                              c)

-- Convert a digit to superscript character
superdigit :: Int -> Char
-------------------------
superdigit d = toEnum (case List.lookup d [(0, 8304), (1, 0185),
                                           (2, 0178), (3, 0179),
                                           (4, 8308), (5, 8309),
                                           (6, 8310), (7, 8311),
                                           (8, 8312), (9, 8313)] of
                       Just c -> c
                       Nothing -> error "Function superdigit applies to digits only")

-- Superscripts a string
superscript :: String -> String
-------------------------------
superscript = List.map (\c -> if isDigit c then
                                superdigit (digitToInt c)
                              else
                                c)

-----------------------------------------
-------- Error generation ---------------

data Error =
    -- Lexing / parsing
    ParsingError String
  | LexingError String
    -- Interpreter
  | UnboundVariable String Extent
    -- Type inference
  | TypeMismatch String String
  | RecursiveType String String
    -- Others
  | CustomError String Extent

instance Show Error where
  show (ParsingError s) = "Parsing error: " ++ s
  show (LexingError s) = "Lexing error: " ++ s
  
  show (UnboundVariable s ex) = show ex ++ ": Not in scope: variable " ++ s
  
  show (TypeMismatch t u) = "Couldn't match expected type '" ++ t ++ "' with actual type '" ++ u ++ "'"
  show (RecursiveType t u) = "Recursive check: cannot construct the infinite type: " ++ t ++ " = " ++ u

  show (CustomError s ex) = if ex == extent_unknown then
                              "Error: " ++ s
                            else
                              show ex ++ ": Error: " ++ s

data Computed a =
    Ok a            -- Success !
  | Failed Error    -- The computation failed

instance Monad Computed where
  return a = Ok a
  fail s = Failed (CustomError s extent_unknown)
  obj >>= action = case obj of
                   Ok a -> action a
                   Failed e -> Failed e

-- Since fail takes only a string as argument, we need this function to return an specific error
error_fail :: Error -> Computed a
---------------------------------
error_fail e = Failed e

-----------------------------------------
------ Manipulation of bindings ---------

-- Binding application
apply_binding :: [(Int, Int)] -> Int -> Int
-----------------------------------
apply_binding b a =
  case List.lookup a b of
  Just a' -> a'
  Nothing -> a


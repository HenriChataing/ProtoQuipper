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
------ Manipulation of bindings ---------

-- Binding application
apply_binding :: [(Int, Int)] -> Int -> Int
-----------------------------------
apply_binding b a =
  case List.lookup a b of
  Just a' -> a'
  Nothing -> a


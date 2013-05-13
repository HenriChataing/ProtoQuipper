module Utils where

import Data.Char as Char

import Data.Map as Map
import Data.List as List

{-
  Some string manipulation functions
-}

-- Convert a digit to subscript character
subDigit :: Int -> Char
-----------------------
 -- 8320 is decimal for 2080 -- Subscript digits are \x2080 .. \x2089
subDigit d = toEnum (8320 + d)

-- Subscripts a string
subscript :: String -> String
-----------------------------
subscript = List.map (\c -> if isDigit c then
                              subDigit (digitToInt c)
                            else
                              c)

-- Convert a digit to superscript character
superDigit :: Int -> Char
-------------------------
superDigit d = toEnum (case List.lookup d [(0, 8304), (1, 0185),
                                           (2, 0178), (3, 0179),
                                           (4, 8308), (5, 8309),
                                           (6, 8310), (7, 8311),
                                           (8, 8312), (9, 8313)] of
                       Just c -> c
                       Nothing -> error "Function superDigit applies to digits only")

-- Superscripts a string
superscript :: String -> String
-------------------------------
superscript = List.map (\c -> if isDigit c then
                                superDigit (digitToInt c)
                              else
                                c)

-- Binding application
apply :: [(Int, Int)] -> Int -> Int
-----------------------------------
apply b a =
  case List.lookup a b of
  Just a' -> a'
  Nothing -> a


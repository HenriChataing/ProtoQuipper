module Utils where

import Data.Char

-- Convert a digit to subscript character
subDigit :: Int -> Char
-----------------------
 -- 8320 is decimal for 2080 -- Subscript digits are \x2080 .. \x2089
subDigit d = toEnum (8320 + d)

-- Subscripts a string
subscript :: String -> String
-----------------------------
subscript = map (\c -> if isDigit c then
                         subDigit (digitToInt c)
                       else
                         c)

-- Convert a digit to superscript character
superDigit :: Int -> Char
-------------------------
superDigit d = toEnum (case lookup d [(0, 8304), (1, 0185),
                                      (2, 0178), (3, 0179),
                                      (4, 8308), (5, 8309),
                                      (6, 8310), (7, 8311),
                                      (8, 8312), (9, 8313)] of
                       Just c -> c
                       Nothing -> error "Function superDigit applies to digits only")

-- Superscripts a string
superscript :: String -> String
-------------------------------
superscript = map (\c -> if isDigit c then
                           superDigit (digitToInt c)
                         else
                           c)

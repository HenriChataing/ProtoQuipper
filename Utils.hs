-- | This module contains some useful string manipulation functions, such as functions to change the position of
-- characters to superscript or subscript ..
module Utils where

import Parsing.Localizing

import System.FilePath.Posix as P

import Data.Char as Char
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List as List


-- | Converts a digit to the subscript equivalent character.
subdigit :: Int -> Char
 -- 8320 is decimal for 2080 -- Subscript digits are \x2080 .. \x2089
subdigit d = toEnum (8320 + d)


-- | Converts a string to subscript. Note that only the digits are
-- transposed to superscript (the tables are not complete).
subscript :: String -> String
subscript = List.map (\c -> if isDigit c then
                              subdigit (digitToInt c)
                            else
                              c)


-- | Converts a digit to the equivalent superscript character.
superdigit :: Int -> Char
superdigit d = toEnum (case List.lookup d [(0, 8304), (1, 0185),
                                           (2, 0178), (3, 0179),
                                           (4, 8308), (5, 8309),
                                           (6, 8310), (7, 8311),
                                           (8, 8312), (9, 8313)] of
                       Just c -> c
                       Nothing -> error "Function superdigit applies to digits only")


-- | Same as subscript, converts a string to superscript, but only the digits.
superscript :: String -> String
superscript = List.map (\c -> if isDigit c then
                                superdigit (digitToInt c)
                              else
                                c)


-- | Prints a variable, represented by its unique id, as X^n, where X is a character symbol
-- and n the id.
supervar :: Char -> Int -> String
supervar x n =
  x:(show n)
--  x:(superscript $ show n)


-- | Prints a variable, represented by its unique id, as X_n, where X is a character symbol
-- and n the id.
subvar :: Char -> Int -> String
subvar x n =
  x:(show n)
--  x:(subscript $ show n)


-- | Returns the name of the module encoded by the file f.
module_of_file :: FilePath -> String
module_of_file f =
  let (init:body) = (P.dropExtension . P.takeFileName) f in
  (Char.toUpper init):body


-- | Performs the disjoint union of a list of sets.
disjoint_union :: Eq a => [[a]] -> [a]
disjoint_union [] = []
disjoint_union (l:restl) =
  let disunion = disjoint_union restl in
  (l \\ disunion) ++ (disunion \\ l)

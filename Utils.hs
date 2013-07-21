module Utils where

import Localizing

import System.FilePath.Posix as P

import Data.Char as Char
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List as List

-- | String manipulation functions | --


-- | Convert a digit to subscript character
subdigit :: Int -> Char
 -- 8320 is decimal for 2080 -- Subscript digits are \x2080 .. \x2089
subdigit d = toEnum (8320 + d)


-- | Subscripts a string
-- Only the digits are transposed to superscript
subscript :: String -> String
subscript = List.map (\c -> if isDigit c then
                              subdigit (digitToInt c)
                            else
                              c)


-- Convert a digit to superscript character
superdigit :: Int -> Char
superdigit d = toEnum (case List.lookup d [(0, 8304), (1, 0185),
                                           (2, 0178), (3, 0179),
                                           (4, 8308), (5, 8309),
                                           (6, 8310), (7, 8311),
                                           (8, 8312), (9, 8313)] of
                       Just c -> c
                       Nothing -> error "Function superdigit applies to digits only")


-- | Superscripts a string
superscript :: String -> String
superscript = List.map (\c -> if isDigit c then
                                superdigit (digitToInt c)
                              else
                                c)


-- | Prints a variable, represented by its unique id, as X^n, where X is a character symbol
-- and n the id
supervar :: Char -> Int -> String
supervar x n =
  x:(superscript $ show n)


-- | Prints a variable, represented by its unique id, as X_n, where X is a character symbol
-- and n the id
subvar :: Char -> Int -> String
subvar x n =
  x:(subscript $ show n)


-- | Return the name of the module coded in file f
module_of_file :: FilePath -> String
module_of_file f =
  let (init:body) = (P.dropExtension . P.takeFileName) f in
  (Char.toUpper init):body

-----------------------------------------
------ Manipulation of bindings ---------

-- Binding application
apply_binding :: [(Int, Int)] -> Int -> Int
-----------------------------------
apply_binding b a =
  case List.lookup a b of
  Just a' -> a'
  Nothing -> a


-- Perform the disjoint union of the list of sets
disjoint_union :: Eq a => [[a]] -> [a]
disjoint_union [] = []
disjoint_union (l:restl) =
  let disunion = disjoint_union restl in
  (l \\ disunion) ++ (disunion \\ l)

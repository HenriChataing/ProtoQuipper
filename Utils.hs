-- | This module contains some useful string manipulation functions, such as functions to change the position of
-- characters to superscript or subscript.
module Utils where

import Parsing.Location

import System.FilePath.Posix as P

import Data.Char as Char
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List as List


-- | Convert a string to uppercase.
string_toUpper :: String -> String
string_toUpper [] = []
string_toUpper (h:t) = Char.toUpper h : t


-- | Convert a digit to the equivalent Unicode subscript character.
subdigit :: Int -> Char
 -- Subscript digits are \x2080 .. \x2089
subdigit d = toEnum (0x2080 + d)


-- | Convert all the digits in a string to subscript. Note that
-- non-digit characters are left unchanged.
subscript :: String -> String
subscript = List.map (\c -> if isDigit c then
                              subdigit (digitToInt c)
                            else
                              c)


-- | Convert a digit to the equivalent Unicode superscript character.
superdigit :: Int -> Char
superdigit d = toEnum (case List.lookup d [(0, 0x2070), (1, 0x00b9),
                                           (2, 0x00b2), (3, 0x00b3),
                                           (4, 0x2074), (5, 0x2075),
                                           (6, 0x2076), (7, 0x2077),
                                           (8, 0x2078), (9, 0x2079)] of
                       Just c -> c
                       Nothing -> error "Function superdigit applies to digits only")


-- | Convert all the digits in a string to superscript. Note that
-- non-digit characters are left unchanged.
superscript :: String -> String
superscript = List.map (\c -> if isDigit c then
                                superdigit (digitToInt c)
                              else
                                c)


-- | Print a variable, represented by its unique id, as /X/^/n/ or /X//n/, where /X/ is a character symbol
-- and /n/ the id.
-- 
-- Note: printing as Unicode superscripts is currently disabled, as
-- this is not portable.
supervar :: Char -> Int -> String
supervar x n =
  x:(show n)
--  x:(superscript $ show n)


-- | Prints a variable, represented by its unique id, as /X/_/n/ or /X//n/, where /X/ is a character symbol
-- and /n/ the id.
-- 
-- Note: printing as Unicode subscripts is currently disabled, as
-- this is not portable.
subvar :: Char -> Int -> String
subvar x n =
  x:(show n)
--  x:(subscript $ show n)


-- | Return the name of the module encoded by the file /f/.
module_of_file :: FilePath -> String
module_of_file f =
  let name = (P.dropExtension . P.takeFileName) f in
  string_toUpper name


-- | Input a list of sets, and output the set of those elements that
-- occur in exactly one of the given sets. 
-- 
-- Note that this is not a pairwise operation: 
-- 
-- > linear_union [x,y,z]
-- 
-- is not the same as
-- 
-- > linear_union [x, linear_union [y,z]].
linear_union :: Eq a => [[a]] -> [a]
linear_union l =
  let all = List.concat l in
  List.concat $ List.map (\a -> let alla = all \\ a in
                                a \\ alla) l

-- | Delete whitespace from the end of a string.
trim_end :: String -> String
trim_end [] = []
trim_end (h:t) 
  | isSpace h =
    if t' == "" then "" else h:t'
  | otherwise =
    h:t'
  where
    t' = trim_end t

-- | Check whether the first string is a suffix of the second one,
-- possibly followed by whitespace.
string_ends_with :: String -> String -> Bool 
string_ends_with suffix string = List.isSuffixOf suffix (trim_end string)



-- | Definition of a quantum data type.
data QType =
    QQubit
  | QUnit
  | QVar Int
  | QTensor [QType]
  deriving (Eq, Show, Ord)

-- | The type of the associated circuits.
type CircType =
  (QType, QType)



-- | Return True if and only if the type @Qubit@ appears at least once in the given type.
has_qubits :: QType -> Bool
has_qubits (QTensor qlist) =
  List.or $ List.map has_qubits qlist
has_qubits QQubit = True
has_qubits _ = False

 


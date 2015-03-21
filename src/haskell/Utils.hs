-- | This module contains some useful string manipulation functions, such as functions to change the position of
-- characters to superscript or subscript. The definition of some types used throughout the transformation are placed here as well.
module Utils where

import Parsing.Location

import System.FilePath.Posix as P

import Data.Char as Char
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List as List


-------------------------------------------------
-- ** String manipulation.


-- | Convert the first character of a string to uppercase.
capitalize :: String -> String
capitalize [] = []
capitalize (h:t) = Char.toUpper h : t


-- | Convert the first character of a string to lowercase.
uncapitalize :: String -> String
uncapitalize [] = []
uncapitalize (h:t) = Char.toLower h : t


-- |  Convert a whole string to lower case.
toLower :: String -> String
toLower = List.map Char.toLower


-- |  Convert a whole string to lower case.
toUpper :: String -> String
toUpper = List.map Char.toUpper


-- | Convert a digit to the equivalent Unicode subscript character.
subdigit :: Int -> Char
 -- Subscript digits are \x2080 .. \x2089
subdigit d = toEnum (0x2080 + d)


-- | Convert all the digits in a string to subscript. Note that
-- non-digit characters are left unchanged.
subscript :: String -> String
subscript = List.map (\c ->
  if isDigit c then
    subdigit (digitToInt c)
  else
    c)


-- | Convert a digit to the equivalent Unicode superscript character.
superdigit :: Int -> Char
superdigit d = toEnum (
  case List.lookup d [
        (0, 0x2070), (1, 0x00b9),
        (2, 0x00b2), (3, 0x00b3),
        (4, 0x2074), (5, 0x2075),
        (6, 0x2076), (7, 0x2077),
        (8, 0x2078), (9, 0x2079)] of
    Just c -> c
    Nothing -> error "Function superdigit applies to digits only")


-- | Convert all the digits in a string to superscript. Note that
-- non-digit characters are left unchanged.
superscript :: String -> String
superscript = List.map (\c ->
  if isDigit c then
    superdigit (digitToInt c)
  else
    c)


-- | Prints a variable with a string prefix.
prevar :: String -> Int -> String
prevar x n =
  x ++ show n


-- | Return the name of the module based on the file name.
moduleNameOfFile :: FilePath -> String
moduleNameOfFile f =
  let name = (P.dropExtension . P.takeFileName) f in
  capitalize name

-- | Return the name of the module based on the file name.
fileOfModuleName :: String -> String -> String
fileOfModuleName moduleName extension =
  uncapitalize moduleName ++ extension

-- | Replace the special characters non accepted in C functiona names by their unicode number.
remove_specials :: String -> String
remove_specials =
  List.concat . List.map (\c ->
    if isAlphaNum c || c == '_' then
      [c]
    else
      "_" ++ show (ord c) ++ "_"
  )



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
  List.concat $ List.map (\a ->
        let alla = all \\ a in
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



-------------------------------------------------
-- ** General types.

-- | A recursive flag. This is used in the expression 'ELet' to indicate
-- whether the binding is recursive or not. The parser only allows functions (and not arbitrary values)
-- to be declared recursive.
data RecFlag =
    Nonrecursive
  | Recursive
  deriving (Eq)

instance Show RecFlag where
  show Nonrecursive = ""
  show Recursive = "rec"


-- | Type of term (and type) variables.
type Variable = Int

-- | Type of type constants.
type Constant = String

-- | Type of data constructors.
type Datacon = Int

-- | Type of algebraic types.
type Algebraic = Int

-- | Type of type synonyms.
type Synonym = Int



-- | A representation of N u {+oo}.
data Lvl =
    Nth Int      -- ^ Finite number n.
  | Inf          -- ^ Infinity.
  deriving (Show, Eq)


-- | Increment the level.
incr :: Lvl -> Lvl
incr (Nth n) = Nth (n+1)
incr Inf = Inf


-- | Decrement the level.
decr :: Lvl -> Lvl
decr (Nth n) = Nth (n-1)
decr Inf = Inf


-- | The default level, set at 2.
default_lvl :: Lvl
default_lvl = Nth 2


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




-- | This module provides a search structure similar to a map, but organized in layers, each
-- layer corresponding to a scope in the original expression.

module LayeredMap where

import qualified Prelude as P

import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as Map

type LayeredMap k v = [Map k v]


-- | The empty scope map is th singleton list containing the empty map
empty :: LayeredMap k v
empty = [Map.empty]


-- | Push a new layer with the empty map onto the stack
new_scope :: LayeredMap k v -> LayeredMap k v
new_scope m =
  Map.empty:m


-- | Close the top layer, dropping all its mappings
end_scope :: LayeredMap k v -> LayeredMap k v
end_scope [] = []
end_scope (_:layers) = layers


-- | Inserts a new element. The element is automatically inserted in the top
-- layer. If the list is empty, an error is generated
insert :: (P.Ord k) => k -> v -> LayeredMap k v -> LayeredMap k v
insert k v [] = P.error "LayeredMap: empty layer stack"
insert k v (top:rest) = (Map.insert k v top:rest)


-- | Lookup an element. The function searches in every layer, starting from the top, untils it finds
-- one containing the element
lookup :: (P.Ord k) => k -> LayeredMap k v -> Maybe v
lookup _ [] = Nothing
lookup k (top:rest) =
  case Map.lookup k top of
    Just v -> Just v
    Nothing -> lookup k rest

-- | This module provides a structure aimed at variable consing.
-- Specifically, it attributes a unique identification (= Int) to each variable.

module Namespace where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap

-- | The definition of the namespace includes a mapping from ids to strings recording
-- the original names, and a counter to generate new ids
data Namespace = NSpace {
  consing :: IntMap String,
  counter :: Int
}


-- | Create a new namespace, with the counter initialized to zero, and the consing map empty
new_namespace :: Namespace
new_namespace = NSpace {
  consing = IMap.empty,
  counter = 0
}


-- | Register a new variable
register :: String -> Namespace -> (Int, Namespace)
register s namespace =
  let id = counter namespace in
  (id, namespace { consing = IMap.insert id s $ consing namespace, counter = id+1 }) 

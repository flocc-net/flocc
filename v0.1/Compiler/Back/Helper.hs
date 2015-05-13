{-
Copyright 2015 Tristan Aubrey-Jones 
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License. 
-}

{-|
Copyright   : (c) Tristan Aubrey-Jones, 2015
License     : Apache-2
Maintainer  : developer@flocc.net
Stability   : experimental

For more information please see <http://www.flocc.net/>
-}
module Compiler.Back.Helper where

import Data.List (sortBy, intersperse)
import Data.Map.Strict as Data.Map (Map, adjust, insert, member, toList, fromList, union, differenceWith)
import qualified Data.IntMap.Strict as Data.IntMap ()

showMap :: Show k => Show v => Map k v -> String
showMap mp = concat $ intersperse ",\n" $ map show $ toList mp

-- |adjustOrCreate initVal transFunc key inMap tries to adjust the
-- |value at the specified key in the map, but if the key doesn't
-- |exist in the map, creates it with the specified intial value,
-- |and then adjusts it.
adjustOrCreate :: Ord k => a -> (a -> a) -> k -> Map k a -> Map k a
adjustOrCreate initV f key inMap = if member key inMap 
  then adjust f key inMap  
  else adjust f key $ insert key initV inMap

-- |updates pairs map adds all the ket value pairs to the map, replacing
-- |any that are already there
updates :: Ord k => [(k, a)] -> Map k a -> Map k a
updates pairs env1 = env2 `union` env1
  where env2 = Data.Map.fromList pairs

-- |sort projF list. Sorts the list using the elements projected
-- |out by projF.
sortWith :: Ord b => (a -> b) -> [a] -> [a]
sortWith projF l = l'''
  where l' = map (\i -> (projF i, i)) l
        l'' = sortBy (\(a,_) -> \(b,_) -> compare a b) l'
        (_,l''') = unzip l''

-- |getMapChanges afterMap beforeMap. Returns a map containing
-- |all the new entries that have been added in afterMap, and all
-- |members that have different values to those in beforeMap.
getMapChanges :: (Eq v, Ord k) => Map k v -> Map k v -> Map k v
getMapChanges = differenceWith (\af -> \bf -> if af /= bf then Just af else Nothing)

-- |match v1 otherVs. Return true if
-- |all otherVs equal v.
match :: Eq a => a -> [a] -> Bool
match ty1 (h:r) = (ty1 == h) && (match ty1 r)
match ty1 [] = True

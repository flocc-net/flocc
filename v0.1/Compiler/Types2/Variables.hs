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
module Compiler.Types2.Variables (VarsIn(..), VarSubsts, applyVarSubst, 
  fromList, fromDisjointList, composeVarSubsts, newVars,
  emptyVarSubsts) where

import Compiler.Front.Indices (Idx, IdxSet, newidST)

import Data.Maybe (Maybe(..))
import Data.Set (Set)
import qualified Data.Set (toList)
--import Data.Map.Strict (Map, mapWithKey, union, empty)
--import qualified Data.Map.Strict as Data.Map (map, fromList, lookup, empty)
import Data.IntMap.Strict (IntMap, mapWithKey, union)
import qualified Data.IntMap.Strict as IM

import Control.Monad.State.Strict ( StateT )

-- |A type that contains variables
class VarsIn a where
  isVar :: a -> Maybe Idx
  getVars :: a -> Set Idx
  newVar :: Idx -> a
  applyVarSubsts :: VarSubsts a -> a -> a

-- |Substs is a Map of substitutions from var ids
-- |to terms.
type VarSubsts a = IntMap a

-- |emptyVarSubsts is an empty set of substitutions
emptyVarSubsts :: IntMap a
emptyVarSubsts = IM.empty

-- |applyVarSubst takes a map of substitutions and a var id
-- |and returns the substituted value if there is one, or 
-- |Var i if there isn't.
applyVarSubst :: VarsIn a => VarSubsts a -> Idx -> a
applyVarSubst subs i = case IM.lookup i subs of
  Just b -> b
  Nothing -> newVar i

-- |fromList takes a list of (var id, VarsIn) pairs
-- |and returns a VarSubsts for that list such that
-- |subs are applied from left to right (left first...)
fromList :: VarsIn a => [(Idx, a)] -> VarSubsts a
fromList (h:t) = foldl (\a -> \b -> composeVarSubsts (fromDisjointList [b]) a) (fromDisjointList [h]) t
fromList [] = emptyVarSubsts

-- |fromDisjointList takes a list of disjoint (Var id, VarsIn) pairs
-- |and returns a VarSubsts.
fromDisjointList :: VarsIn a => [(Idx, a)] -> VarSubsts a
fromDisjointList l = IM.fromList l

-- |composeSubsts a b sequentially composes a and b
-- |such that a is applied after b.
composeVarSubsts :: VarsIn a => VarSubsts a -> VarSubsts a -> VarSubsts a
composeVarSubsts a b = (IM.map (\bv -> applyVarSubsts a bv) b) `union` a

-- |newVars varsToChange a, takes
-- |a list of var ids to change, and an instance of VarsIn and returns
-- |the same VarsIn a with the var ids to change replaced with new ones
-- |from the newids in the state monad.
newVars :: (Monad m, VarsIn a) => Set Idx -> a -> StateT IdxSet m a
newVars varsToChange a = do
  subList <- mapM (\i -> do i' <- newidST 0; return (i, newVar i')) (Data.Set.toList varsToChange)
  return $ applyVarSubsts (fromDisjointList subList) a 



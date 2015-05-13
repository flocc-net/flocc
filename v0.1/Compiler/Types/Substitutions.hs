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
module Compiler.Types.Substitutions where

import Compiler.Front.Common (Mappable(monadicMap), Counted(..), incCount)

import qualified Data.Map.Strict as M
import Data.Functor.Identity (runIdentity)

type SubstMap t = M.Map t t 

-- |emptySubstMap is an empty set of substitutions
emptySubstMap :: M.Map a a
emptySubstMap = M.empty

applySubsts :: Ord a => SubstMap a -> a -> a
applySubsts subs val = case M.lookup val subs of
  Just b -> b
  Nothing -> val

-- |...
applySubstsMap :: (Ord a, Monad m, Mappable a) => SubstMap a -> a -> m a
applySubstsMap subs val = monadicMap (return.(applySubsts subs)) val

{-applyAndCountSubsts :: (Ord a, Monad m, Counted a) => SubstMap a -> a -> m a
applyAndCountSubsts subs val = do
  let cnt = getCount val
  case M.lookup val subs of
    Just val' -> 
    Nothing   -> return val

applyAndCountSubstsMap subs val = monadicMap (applyAndCountSubsts subs) val-}

-- |fromDisjointList takes a list of disjoint (Var id, VarsIn) pairs
-- |and returns a VarSubsts.
fromDisjointList :: Ord a => [(a, a)] -> SubstMap a
fromDisjointList l = M.fromList l

-- |composeSubsts a b sequentially composes a and b
-- |such that a is applied after b.
composeSubsts :: (Ord a, Mappable a) => SubstMap a -> SubstMap a -> SubstMap a
composeSubsts a b = (M.map (\bv -> runIdentity $ applySubstsMap a bv) b) `M.union` a


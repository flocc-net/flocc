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
module Compiler.Front.Indices (Idx, IdxSet, IdxMonad, 
  getnid, newid, newid', newid'', getid', 
  getidST, newidST, newidST', getNextIdxST, setMinIndices) where

import Control.Monad ( mapM )
import Control.Monad.State.Strict

type Idx = Int
type IdxSet = [Int]
type IdxMonad m = StateT IdxSet m 

-- |Creates a new id for the given entry in the IdxSet, incrementing the set and returning the
-- |modified one 
nid :: Int -> IdxSet -> IdxSet -> IdxSet
nid i hl (h:t) = if (i == 0) then (nid (i-1) ((h+1):hl) t) else (nid (i-1) (h:hl) t)
nid i hl [] = reverse hl

-- |Gets the next id for a column in the idx set, and
-- |returns that id, and the updated list.
getnid :: Int -> IdxSet -> (Idx, IdxSet)
getnid n s = let id = (s !! n) in (id, nid n [] s)

getNextIdxST :: Monad m => String -> Int -> IdxMonad m Idx
getNextIdxST msg col = do
  curMax <- get
  if col >= (length curMax) then error $ msg ++ ": index too large " ++ (show col) ++ " " ++ (show curMax) else return ()
  return $ (curMax !! col)+1

setMinIndices :: Monad m => Idx -> IdxMonad m ()
setMinIndices minIdx = do
  modify (\st -> map (max minIdx) st)
  return ()

-- |Creates a new id (for the list of ids specified by the first paramter)
newid :: Int -> State IdxSet Idx
newid i = do
    curMax <- get
    modify (\max -> (nid i [] max))
    return (curMax !! i)

-- |Returns the id in the map list if it exists. if it does not, creates a new one 
-- |adds it to the map
newid' :: Int -> Idx -> StateT [(Idx, Idx)] (State IdxSet) Idx
newid' i v = do
  mp <- get
  case lookup v mp of 
    Just v' -> return v'
    Nothing -> do v' <- lift (newid i)
                  modify (\mp' -> (v,v') : mp')
                  return v'

-- |Returns the id in the map list if it exists. if it does not, creates a new one 
-- |adds it to the map, using a state transformer.
newidST' :: Monad m => Int -> Idx -> StateT [(Idx, Idx)] (StateT IdxSet m) Idx
newidST' i v = do
  mp <- get
  case lookup v mp of 
    Just v' -> return v'
    Nothing -> do v' <- lift (newidST i)
                  modify (\mp' -> (v,v') : mp')
                  return v'

-- |Creates a new id (for the list of ids specified by the first parameter) using
-- |a state transformer, rather than a state monad.
newid'' :: Monad m => Int -> StateT IdxSet m Idx
newid'' i = do
  curMax <- get
  modify (\max -> (nid i [] max))
  return (curMax !! i)

newidST :: Monad m => Int -> StateT IdxSet m Idx
newidST = newid''

-- |Looks up the id in the list, and returns the replacement if it exists
-- |or the original if it doesnt 
getid' :: Idx -> StateT [(Idx, Idx)] (State IdxSet) Idx
getid' v = do
  mp <- get
  case lookup v mp of
    Just v' -> return v'
    Nothing -> return v

-- |Looks up the id in the list, and returns the replacement if it exists
-- |or the original if it doesnt 
getidST :: Monad m => Idx -> StateT [(Idx, Idx)] (StateT IdxSet m) Idx
getidST v = do
  mp <- get
  case lookup v mp of
    Just v' -> return v'
    Nothing -> return v

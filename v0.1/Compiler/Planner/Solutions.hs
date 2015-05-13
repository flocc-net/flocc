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
module Compiler.Planner.Solutions where

import Compiler.Front.Common
import Data.List (intercalate)

type SolId = [Int]
data SolCost = 
    SolErr String
  | SolSucc Float
  | SolTimeout Float
  deriving (Eq, Ord, Show, Read)

isSolErr :: SolCost -> Bool
isSolErr (SolErr _) = True
isSolErr _ = False

isSolSucc :: SolCost -> Bool
isSolSucc (SolSucc f) = True
isSolSucc _ = False

isSolTimeout :: SolCost -> Bool
isSolTimeout (SolTimeout _) = True
isSolTimeout _ = False

prettySolCost :: SolCost -> String
prettySolCost c = case c of
  SolErr c -> "SolErr " ++ c
  _ -> show c

type AvgSolCost = Float

avgCost :: [SolCost] -> AvgSolCost
avgCost [(SolErr _)] = 60.0*60.0
avgCost l = (sum succs) + (sum tmouts) / (fromIntegral $ length succs + length tmouts)
  where succs = map (\(SolSucc c) -> c) $ filter isSolSucc l
        tmouts = map (\(SolTimeout c) -> c) $ filter isSolTimeout l

data SolMetaInfo = SolMetaInfo {
  siCastCost :: Int, -- just the cost estimate
  siNumCastSols :: Int, -- number of cast solutions found
  siTimeCastSols :: Float -- time taken to find those solutions in seconds.
} deriving (Show, Read)

loadMetaInfo :: String -> IO SolMetaInfo
loadMetaInfo path = do
  str <- readFileForce path
  let costEst = read str
  return costEst

saveMetaInfo :: String -> SolMetaInfo -> IO ()
saveMetaInfo path info = do
  let str = show info
  writeFileForce path str
  return ()

createFilename :: SolId -> String
createFilename sid = "sol" ++ (intercalate "_" $ map show sid)

numRedistSolsToTry :: Int
numRedistSolsToTry = 2



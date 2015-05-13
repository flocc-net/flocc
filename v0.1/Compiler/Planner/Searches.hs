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
module Compiler.Planner.Searches (exaustiveSearch, tryAllSearches, evalAllSearches, showAllStats, showAllRules) where

import Compiler.Front.Common
import Compiler.Planner.Solutions
import Compiler.Planner.SolExec
import Compiler.Planner.SearchCache
import Compiler.Planner.Rules

import Data.Maybe (fromMaybe, isJust, fromJust)
import Data.List (sortBy, intercalate, nub, find, findIndex)
import qualified Data.Map as DM
import Control.Monad.State.Strict (StateT, runStateT, evalStateT, execStateT, lift, get, gets, modify)
import Data.Time.Clock
import Numeric 
import System.Random (randomRIO)
import Debug.Trace (trace)

--formatFloatN floatNum numOfDecimals = showFFloat (Just numOfDecimals) floatNum ""

type TimeoutFun = SearchM Int -- how long to run sol before killing
type PrunePred = SolId -> SearchM Bool -- don't get cost for sol
type TerminatePred = SearchM Bool -- terminate search

data SearchStats = SearchStats {
    statMean :: AvgSolCost,
    statMax :: AvgSolCost,
    statMin :: AvgSolCost,
    statStddev :: AvgSolCost
  } deriving (Show)

initStats :: SearchStats 
initStats = SearchStats {
    statMean = 0.0,
    statMax = -10000.0,
    statMin = 100000.0,
    statStddev = 0.0
  }

stddev :: Int -> AvgSolCost -> [AvgSolCost] -> AvgSolCost
stddev n mean xl = sqrt $ sm / (realToFrac n)
  where sm = sum $ map (\x -> (x-mean)*(x-mean) ) xl

data SearchSt = SearchSt {
    schBestSol :: Maybe SolId,
    schBestCost :: AvgSolCost,
    schBestInfo :: Maybe SolMetaInfo,
    schWorstSol :: Maybe SolId,
    schWorstCost :: AvgSolCost,
    schWorstInfo :: Maybe SolMetaInfo,
    schAllCosts :: [AvgSolCost],
    schSolsVisited :: DM.Map SolId (Int, Float),
    schSolCount :: Int,
    schSolTime :: Float,
    schTimeout :: TimeoutFun,
    schPrune :: PrunePred,
    schTerminate :: TerminatePred,
    schTerminated :: Bool,
    schStats :: SearchStats,
    schSpaceSize :: Int,
    schVisitCount :: Int
  } 

maxVisits :: SearchSt -> Bool
maxVisits st = {-trace ("visit count: " ++ (show vc) ++ "; space size: " ++ (show sz) ++ "\n") $-} vc > (5 * sz)
  where sz = schSpaceSize st
        vc = schVisitCount st

instance Show SearchSt where
  show (SearchSt bestSol bestCost bestInfo worstSol worstCost worstInfo allCosts _ solCount solTime _ _ _ _ stats sz visitCount) = 
         (show bestSol) ++ "\n" ++ (show bestCost) ++ "\n" ++ (show bestInfo) ++ "\n\n" ++
         (show worstSol) ++ "\n" ++ (show worstInfo) ++ "\n\n" ++
         (show allCosts) ++ "\n\n" ++
         (show solCount) ++ "\n" ++ (show solTime) ++ "\n\n" ++
         (show stats) ++ "\n\n" ++ (show sz) ++ "\n" ++ (show visitCount) ++ "\n"

initSearchSt = SearchSt {
    schBestSol = Nothing,
    schBestCost = 9999999.9,
    schBestInfo = Nothing,
    schWorstSol = Nothing,
    schWorstCost = 0.0,
    schWorstInfo = Nothing,
    schAllCosts = [],
    schSolsVisited = DM.empty,
    schSolCount = 0,
    schSolTime = 0.0,
    schTimeout = constTimeout,
    schPrune = dontPrune,
    schTerminate = searchToEnd,
    schTerminated = False,
    schStats = initStats,
    schSpaceSize = 0,
    schVisitCount = 0
  }

type SearchM = StateT SearchSt SCacheM

-- |Search through all possible solutions
searchToEnd :: TerminatePred
searchToEnd = do
  numTried <- gets (DM.size . schSolsVisited)
  numToTry <- gets schSpaceSize
  maxedOut <- gets maxVisits
  let stop = (numTried >= numToTry) || maxedOut
  return {- trace ("searchToEnv " ++ (show numTried) ++ " of " ++ (show numToTry) ++  " so stop? " ++ (show stop) ++ "\n") -} stop

-- |Search for 10mins of runtime
searchForHalfMin :: TerminatePred
searchForHalfMin = do
  maxedOut <- gets maxVisits
  tm <- gets schSolTime
  let stop = (tm > 30.0) || maxedOut
  return stop

-- |Search until the best is twice as good as the average
searchTilAboveAvg :: TerminatePred
searchTilAboveAvg = do
  best <- gets schBestCost
  mean <- gets (statMean . schStats)
  maxedOut <- gets maxVisits
  return $ (best < (mean / 2.0)) || maxedOut

-- |Search until the best is 2 standard deviations above the average
searchTilAboveStddev :: TerminatePred
searchTilAboveStddev = do
  best <- gets schBestCost
  mean <- gets (statMean . schStats)
  dev <- gets (statStddev . schStats)
  maxedOut <- gets maxVisits
  return $ (best < (mean - 2.0*dev)) || maxedOut

-- |Search until half of the states in the statespace have been explored
searchTilHalfTried :: TerminatePred
searchTilHalfTried = do
  numTried <- gets schSolCount
  numToTry <- gets schSpaceSize
  maxedOut <- gets maxVisits
  return $ (numTried > (round $ (realToFrac numToTry) / 2.0)) || maxedOut

-- |Search until half of the states in the statespace have been explored
searchTilQuartTried :: TerminatePred
searchTilQuartTried = do
  numTried <- gets schSolCount
  numToTry <- gets schSpaceSize
  maxedOut <- gets maxVisits
  return $ (numTried > (round $ (realToFrac numToTry) / 4.0)) || maxedOut

-- |Search through all possible solutions
searchTenSols :: TerminatePred
searchTenSols = do
  numTried <- gets (DM.size . schSolsVisited)
  maxedOut <- gets maxVisits
  let stop = (numTried >= 10) || maxedOut
  return {- trace ("searchToEnv " ++ (show numTried) ++ " of " ++ (show numToTry) ++  " so stop? " ++ (show stop) ++ "\n") -} stop

-- |Search through all possible solutions
search10Sols :: TerminatePred
search10Sols = do
  numTried <- gets (DM.size . schSolsVisited)
  maxedOut <- gets maxVisits
  let stop = (numTried >= 10) || maxedOut
  return {- trace ("searchToEnv " ++ (show numTried) ++ " of " ++ (show numToTry) ++  " so stop? " ++ (show stop) ++ "\n") -} stop

-- |Search through all possible solutions
search15Sols :: TerminatePred
search15Sols = do
  numTried <- gets (DM.size . schSolsVisited)
  maxedOut <- gets maxVisits
  let stop = (numTried >= 15) || maxedOut
  return {- trace ("searchToEnv " ++ (show numTried) ++ " of " ++ (show numToTry) ++  " so stop? " ++ (show stop) ++ "\n") -} stop

-- |Search through all possible solutions
search20Sols :: TerminatePred
search20Sols = do
  numTried <- gets (DM.size . schSolsVisited)
  maxedOut <- gets maxVisits
  let stop = (numTried >= 20) || maxedOut
  return {- trace ("searchToEnv " ++ (show numTried) ++ " of " ++ (show numToTry) ++  " so stop? " ++ (show stop) ++ "\n") -} stop

-- |Terminates when the last num costs are all within a
-- |threshold proportion of each other.
searchTilSameCosts :: Int -> Float -> TerminatePred
searchTilSameCosts num threshold = do
  maxedOut <- gets maxVisits
  if maxedOut 
  then return True
  else do
    allCosts <- gets schAllCosts
    let l = take num allCosts
    case l of
      [] -> return False
      [h] -> return False
      (h:rest) -> do
        let lower = h - (h* threshold)
        let upper = h + (h* threshold)
        let ll = map (\c -> (c >= lower) && (c <= lower)) rest
        return $ and ll

searchTilNoneNew :: TerminatePred
searchTilNoneNew = gets maxVisits

terminatePreds :: [(String, TerminatePred)]
terminatePreds = [
  ("searchToEnd", searchToEnd), 
  ("search10Sols", search10Sols),
  ("search15Sols", search15Sols),
  ("search20Sols", search20Sols),
  --("searchForHalfMin", searchForHalfMin),
  ("searchTilAboveAvg", searchTilAboveAvg), 
  ("searchTilAboveStddev", searchTilAboveStddev),
  ("searchTilHalfTried", searchTilHalfTried),
  ("searchTilQuartTried", searchTilQuartTried),
  ("tilNoneNew", searchTilNoneNew),
  ("searchTilSameCosts(n=3,th=0.1)", searchTilSameCosts 3 0.1),
  ("searchTilSameCosts(n=2,th=0.1)", searchTilSameCosts 2 0.1),
  ("searchTilSameCosts(n=3,th=0.2)", searchTilSameCosts 3 0.2),
  ("searchTilSameCosts(n=2,th=0.2)", searchTilSameCosts 2 0.2),
  ("searchTilSameCosts(n=4,th=0.1)", searchTilSameCosts 4 0.1),  
  ("searchTilSameCosts(n=4,th=0.2)", searchTilSameCosts 4 0.2)
 ]

-- |Constant timeout
constTimeout :: TimeoutFun
constTimeout = do
  return maxTime

-- |Min sol cost timeout
minCostTimeout :: TimeoutFun
minCostTimeout = (gets schBestCost) >>= (return . round)

-- |Min sol cost times 2
twiceMinCostTimeout :: TimeoutFun
twiceMinCostTimeout = gets schBestCost >>= (return . round . (*2.0))

timeoutFuns :: [(String, TimeoutFun)]
timeoutFuns = [
  ("constTimeout", constTimeout),
  ("minCostTimeout", minCostTimeout), 
  ("twiceMinCostTimeout", twiceMinCostTimeout)]

-- |Dont prune solutions, try them all
dontPrune :: PrunePred
dontPrune sid = return False

orderMagCastCostPrune :: PrunePred
orderMagCastCostPrune sid = do
  -- if we have info for best and current
  -- compare, otherwise dont prune sid
  best <- gets schBestInfo
  case best of 
    Nothing -> return False
    Just bestInfo -> do
      -- get info for sid
      cur <- lift $ getSolInfo sid
      case cur of
        Nothing -> return False
        Just curInfo -> do
          -- compare cast cost ests
          let bestEst = siCastCost bestInfo
          let curEst = siCastCost curInfo
          return (curEst > (bestEst * 10))

nonZeroCostPrune :: PrunePred
nonZeroCostPrune sid = do
  -- get info for sid
  cur <- lift $ getSolInfo sid
  case cur of
    Nothing -> return False
    Just curInfo -> do
      -- compare cast cost ests
      let curEst = siCastCost curInfo
      return (curEst > 0)

prunePreds :: [(String, PrunePred)]
prunePreds = [("dontPrune", dontPrune){-, ("nonZeroCostPrune", nonZeroCostPrune){-, ("orderMagCastCostPrune", orderMagCastCostPrune)-}-}]

-- |Return ranges for solution ids
getRanges :: SCacheM [[Int]]
getRanges = do
  -- get search ranges
  ctx <- gets $ (fromMaybe (error "Searches:getRanges: context not loaded!")) . scSolCtx
  let ast = (fromMaybe (error "Searches:getRanges: ast not loaded!")) $ ctxProgramAst ctx
  let rules = ctxRuleset ctx 
  let ruleApps = getRuleApps rules ast
  let ranges = map (\(_,_,r) -> r) ruleApps
  -- add different redist solutions to try to ranges
  let ranges' = ranges ++ [[1..numRedistSolsToTry]]
  return ranges'

getRuleStrs :: SCacheM [([Int], [String])]
getRuleStrs = do
  -- get search ranges
  ctx <- gets $ (fromMaybe (error "Searches:getRuleStrs: context not loaded!")) . scSolCtx
  let ast = (fromMaybe (error "Searches:getRuleStrs: ast not loaded!")) $ ctxProgramAst ctx
  let rules = ctxRuleset ctx 
  let ruleApps = getRuleApps rules ast
  -- get strings
  let names = getAllRuleNames rules ast ruleApps []
  return names

-- |Gets the cost of a solution. Basically visits a solution.
getCost :: [Int] -> SearchM [(SolId, Float)]
getCost sid = do
  -- test if should terminate
  termPred <- gets schTerminate
  term <- termPred
  modify (\st -> st { schTerminated=term })
  case term of
    -- terminate
    True -> return []
    -- keep searching
    False -> do
      -- record this visit
      modify (\st -> st { schVisitCount=(schVisitCount st)+1 })
      -- if already visited, then ignore
      visited <- gets ((DM.lookup sid) . schSolsVisited)
      case visited of
        -- already visited (dont update stats)
        Just (iterCount, searchTime) -> do
          -- get its cost from cache though
          fullCost <- lift $ getSolCost sid
          curTimeout <- lift $ gets (realToFrac . ctxMaxExecTime .  (fromMaybe (error $ "Searches:getCost:no sol context!")) . scSolCtx)
          let cost = min fullCost curTimeout 
          return [(sid, cost)]
        -- not visited so visit now...
        Nothing -> do
          -- see if we should prune this
          pruner <- gets schPrune
          prune <- pruner sid
          case prune of
            -- prune this solution (don't get it's cost)
            True -> do
              -- add to visited map
              iterCount <- gets schSolCount
              searchTime <- gets schSolTime
              modify (\st -> st { schSolsVisited=DM.insert sid (iterCount, searchTime) (schSolsVisited st) })
              -- count this visit, but don't add to time
              modify (\st -> st { schSolCount=(schSolCount st)+1 })
              -- don't get cost
              return [(sid, 5000000.0)]
            -- don't prune it
            False -> do 
              -- get cost and info for this (if cost greater than timeout, then would have killed it, so use timeout as cost)
              fullCost <- lift $ getSolCost sid
              curTimeout <- lift $ gets (realToFrac . ctxMaxExecTime .  (fromMaybe (error $ "Searches:getCost:no sol context!")) . scSolCtx)
              let cost = min fullCost curTimeout 
              info <- lift $ getSolInfo sid
              -- add to visited map (with input about first found)
              iterCount <- gets schSolCount
              searchTime <- gets schSolTime
              modify (\st -> st { schSolsVisited=DM.insert sid (iterCount, searchTime) (schSolsVisited st) })
              modify (\st -> st { schAllCosts=cost:(schAllCosts st) })
              -- update totals
              modify (\st -> st { 
                schSolCount=(schSolCount st)+1, 
                schSolTime=(schSolTime st)+cost })
              -- update best and worst costs
              bestCost <- gets schBestCost
              worstCost <- gets schWorstCost
              let worstCost' = if cost > worstCost then cost else worstCost
              let bestCost' = if cost < bestCost then cost else bestCost
              modify (\st -> st { 
                schBestCost=bestCost',
                schWorstCost=worstCost',
                schBestSol=if cost < bestCost then Just sid else (schBestSol st),
                schWorstSol=if cost > worstCost then Just sid else (schWorstSol st),
                schBestInfo=if cost < bestCost then info else (schBestInfo st),
                schWorstInfo=if cost > worstCost then info else (schWorstInfo st) })
              -- calc other stats (mean and stddev)
              stats <- gets schStats
              modify (\st -> let mean = (schSolTime st) / (realToFrac $ schSolCount st) in
                st { schStats=SearchStats { 
                      statMax=worstCost', 
                      statMin=bestCost',  
                      statMean= mean,
                      statStddev=stddev (schSolCount st) mean (schAllCosts st) } } )
              -- calc new timeout
              timeoutF <- gets schTimeout
              timeout <- timeoutF
              lift $ modify (\st -> st { scSolCtx=fmap (\ctx -> ctx { ctxMaxExecTime=timeout }) (scSolCtx st)  } )
              -- return
              return [(sid, cost)]

quote :: String -> String
quote s = "\"" ++ s ++ "\""

showAllRules :: SCacheM String
showAllRules = do
  strs <- getRuleStrs
  let lines = map (\(sid,names) -> intercalate ", " $ (map (quote . show) sid) ++ (map quote names)) strs
  let txt = unlines lines  
  return txt 

-- |showSolStats sid. Shows the stats about a solution
-- |in CSV format.
showSolStats :: [Int] -> SCacheM String
showSolStats sid = do
  -- make name from sid
  let sidStr = intercalate "_" $ map show sid
  let sidCols = map (quote . show) sid
  -- get stats
  cost <- getSolCost sid
  info <- getSolInfo sid
  case info of
    Nothing -> do
       -- show stats
      let strs = [quote sidStr] ++ sidCols ++
                 [quote (showFFloat Nothing cost ""), quote "?", quote "?"]
      return $ intercalate ", " $ strs
    Just info -> do
      let castCost = siCastCost info
      let numCastSols = siNumCastSols info
      -- show stats
      let strs = [quote sidStr] ++ sidCols ++
                 [quote (showFFloat Nothing cost ""), quote (show castCost), quote (show numCastSols)]
      return $ intercalate ", " $ strs

-- |showAllStats. Returns a CSV with stats for all the solutions of the 
-- |current program.
showAllStats :: SCacheM String
showAllStats = do
  -- get ranges
  ranges <- getRanges
  -- get stats for all sids
  stats <- evalStateT (visitAll (lift . showSolStats) ranges []) initSearchSt
  -- return them
  let hdrs = [quote "SolId"] ++ (map (show . fst) $ zip [0..] ranges) ++
             [quote "Time", quote ("RedistCost"), quote ("NumRedistSols")]
  let hdrStr = intercalate ", " hdrs
  let csv = concat $ map (++"\n") $ (hdrStr:stats)
  return csv

-- |Visit all sids in depth first order (until terminated).
visitAll :: ([Int] -> SearchM a) -> [[Int]] -> [Int] -> SearchM [a]
visitAll f (cur:remRanges) sid = do
  terminated <- gets schTerminated
  case terminated of 
    True -> 
      return []
    False -> do
      l <- mapM (\i -> visitAll f remRanges $ sid ++ [i]) cur
      return $ concat l
visitAll f [] sid = do
  v <- f sid
  lift $ saveCache
  return $ [v]

type SolVisitor a = ([Int] -> SearchM a) -> [[Int]] -> SearchM [a]

-- |Visit all solutions forward depth first search
depthFirstVisitor :: SolVisitor a
depthFirstVisitor f ranges = visitAll f ranges []

-- |visit all solutions backward depth first search
reverseDepthFirstVisitor :: SolVisitor a
reverseDepthFirstVisitor f ranges = depthFirstVisitor f $ map reverse ranges

-- |Explores last part of sid before the first part.
reverseRanges :: SolVisitor a -> ([Int] -> SearchM a) -> [[Int]] -> SearchM [a]
reverseRanges visitor f ranges = visitor (\sid -> f $ reverse sid) $ reverse ranges 

-- |Iterativly creates better populations.
climbVisitor :: ([[Int]] -> [[Int]] -> SearchM [[Int]]) -> [[Int]] -> Int -> ([Int] -> SearchM [(SolId, Float)]) -> [[Int]] -> SearchM [[(SolId, Float)]]
climbVisitor genNext ranges numParents visitor startSids = do
  -- check if terminated
  terminated <- gets {- (trace $ "climb " ++ (show startSids) ++ "\n")-} schTerminated
  case terminated of 
    True -> 
      return []
    False -> do
      -- eval current candidates
      l <- mapM (\sid -> visitor sid) startSids
      let sols = concat l
      -- pick best solutions
      let best = take numParents $ sortBy (\(_,c1) -> \(_,c2) -> compare c1 c2) sols
      -- check there are enough parents (may not be enough if they were pruned)
      if length best < numParents 
      then return [sols] -- have to end search
      else do
        -- generate children from them
        children <- genNext ranges $ map fst best
        -- if no children
        if length children <= 0 
        -- then finish
        then return [sols]
        -- else iterate
        else do
          rec <- climbVisitor genNext ranges numParents visitor children
          return $ rec ++ [sols]

-- |Returns all possible choices for the next app.
genGreedyNext :: [[Int]] -> [[Int]] -> SearchM [[Int]]
genGreedyNext ranges [] = error $ "genGreedyNext: must give at least 1 parent!"
genGreedyNext ranges parents@(p1:[]) = do
  -- get first appIdx to explore
  let nextL = zip [0..] ranges
  let nextIdxMb = find (\(idx,ran) -> length ran > 1) $ nextL
  -- if there is a first appIdx
  case nextIdxMb of
    -- generate children
    Just (nextIdx, ran) -> do
      let prefix = take nextIdx p1
      let suffix = drop (nextIdx+1) p1
      let childs = map (\val -> prefix ++ [val] ++ suffix) ran
      return childs
    -- finished
    Nothing -> return [] -- no more apps, so we're done  
genGreedyNext ranges parents@(p1:p2:_) = do
  -- find which appIdx was explored in last iteration
  let lastIdxMb = findIndex (\(a,b) -> a /= b) $ zip p1 p2
  let lastIdx = fromMaybe (error "genGreedyNext: can't find last expored app idx.") lastIdxMb
  -- get next appIdx to explore
  let nextL = drop (lastIdx+1) $ zip [0..] ranges
  let nextIdxMb = find (\(idx,ran) -> length ran > 1) $ nextL
  -- if there is a next appIdx
  case nextIdxMb of
    -- generate children
    Just (nextIdx, ran) -> do
      let prefix = take nextIdx p1
      let suffix = drop (nextIdx+1) p1
      let childs = map (\val -> prefix ++ [val] ++ suffix) ran
      return childs
    -- finished
    Nothing -> return [] -- no more apps, so we're done

greedyVisitor :: SolVisitor [(SolId, Float)]
greedyVisitor visit ranges = do
  startSid <- lift $ lift $ randSid ranges
  climbVisitor genGreedyNext ranges 2 visit [startSid]

randPair :: (a, a) -> IO a
randPair (a, b) = do
  idx <- randomRIO (True, False)
  case idx of
    True -> return a
    False -> return b

randElem :: Show a => [a] -> IO a
randElem l = do
  idx <- randomRIO (0, (length l)-1)
  return $ listGet "Searches:randElem:" l idx

randSid :: [[Int]] -> IO [Int]
randSid ranges = do
  sid <- mapM (\r -> randElem r) ranges  
  return sid

-- |Completely random children
genRandNext :: Int -> [[Int]] -> [[Int]] -> SearchM [[Int]]
genRandNext numChildren ranges parents = do
  childs <- lift $ lift $ mapM (\_ -> mapM (\range -> do randElem range) ranges) [1..numChildren]
  return childs

-- |Randomly picks numApps apps from ranges. Discards apps that 
-- |only have one possible value.
getRandApps :: Int -> [[Int]] -> IO [Int]
getRandApps numApps ranges = do
  -- get possible apps (where > 1 option)
  let posRanges = filter (\(_,r) -> length r > 1) $ zip [0..] ranges  
  if length posRanges < numApps 
  then error $ "Searches:getRandApps: not enough "++ (show numApps)++" non-singleton ranges: " ++ (show ranges)
  else do
    -- select random apps
    let posApps = map fst posRanges
    l <- mapM (\_ -> randElem posApps) [0..(numApps*3)]
    return $ take numApps $ nub l

-- |Apply random mutations to parents
genRandMutationsNext :: Int -> Int -> [[Int]] -> [[Int]] -> SearchM [[Int]]
genRandMutationsNext numMutations numChildren ranges parents = do
  -- get random mutations
  muts <- lift $ lift $ mapM (\_ -> 
    do apps <- getRandApps numMutations ranges ;
       muts <- mapM (\appIdx -> 
         do newIdx <- randElem (listGet "genRandChangesNext" ranges appIdx); 
            return (appIdx, newIdx)) apps
       return muts) [1..(2*numChildren)]
  -- apply mutations to parents to get children
  childs <- lift $ lift $ mapM (\mut -> 
    do par <- randElem parents;
       let child = map (\(appIdx,curVal) -> fromMaybe curVal $ lookup appIdx mut) $ zip [0..] par ;
       return child) muts
  -- remove duplicates and get requested count
  let childs' = take numChildren $ nub childs
  return childs'

randomMutationsVisitor1 :: SolVisitor [(SolId, Float)]
randomMutationsVisitor1 visit ranges = do
  startSid <- lift $ lift $ randSid ranges
  climbVisitor (genRandMutationsNext 1 4) ranges 2 visit [startSid]

randomMutationsVisitor2 :: SolVisitor [(SolId, Float)]
randomMutationsVisitor2 visit ranges = do
  startSid <- lift $ lift $ randSid ranges
  climbVisitor (genRandMutationsNext 1 4) ranges 1 visit [startSid]

-- |Returns a random change, +1 or -1, clipped to max min rails.
getRandChange :: Int -> Int -> Int -> IO Int
getRandChange mn mx cur = do
  if mx == mn 
  then error $ "Searches:getRandChange: max equals min!"
  else do
    if cur > mx || cur < mn 
    then error $ "Searches:getRandChange: cur out of bounds! " ++ (show mn) ++ " to " ++ (show mx) ++ ", cur = " ++ (show cur)  
    else do
      if cur == mx then return $ cur - 1
      else if cur == mn then return $ cur + 1
      else do
        delta <- randElem [-1, 1]
        return $ cur + delta

-- |Apply random mutations to parents
genRandChangesNext :: Int -> Int -> [[Int]] -> [[Int]] -> SearchM [[Int]]
genRandChangesNext numChanges numChildren ranges parents = do
  -- apply random changes to parents to get children
  childs <- lift $ lift $ mapM (\_ -> 
    do par <- randElem parents;
       apps <- getRandApps numChanges ranges ;
       child <- mapM (\(appIdx,curVal) -> 
         do if elem appIdx apps
            then getRandChange 1 (length $ listGet "genRandChangesNext:get range length." ranges appIdx) curVal
            else return curVal) $ zip [0..] par ;
       return child) [1..(2*numChildren)]
  -- remove duplicates and get requested count
  let childs' = take numChildren $ nub childs
  return childs'

randomChangesVisitor1 :: SolVisitor [(SolId, Float)]
randomChangesVisitor1 visit ranges = do
  startSid <- lift $ lift $ randSid ranges
  climbVisitor (genRandChangesNext 1 4) ranges 2 visit [startSid]

randomChangesVisitor2 :: SolVisitor [(SolId, Float)]
randomChangesVisitor2 visit ranges = do
  startSid <- lift $ lift $ randSid ranges
  climbVisitor (genRandChangesNext 1 4) ranges 1 visit [startSid]

randomChangesVisitor3 :: SolVisitor [(SolId, Float)]
randomChangesVisitor3 visit ranges = do
  startSid <- lift $ lift $ randSid ranges
  climbVisitor (genRandChangesNext 1 2) ranges 1 visit [startSid]

randomChangesVisitor4 :: SolVisitor [(SolId, Float)]
randomChangesVisitor4 visit ranges = do
  startSid <- lift $ lift $ randSid ranges
  climbVisitor (genRandChangesNext 1 3) ranges 1 visit [startSid]

randomChangesVisitor5 :: SolVisitor [(SolId, Float)]
randomChangesVisitor5 visit ranges = do
  startSid <- lift $ lift $ randSid ranges
  climbVisitor (genRandChangesNext 2 2) ranges 1 visit [startSid]

randomChangesVisitor6 :: SolVisitor [(SolId, Float)]
randomChangesVisitor6 visit ranges = do
  startSid <- lift $ lift $ randSid ranges
  climbVisitor (genRandChangesNext 2 3) ranges 1 visit [startSid]

-- |Choose random parents, and randomly select genes from both, and 
-- |mutate genes with probability probMutate.
genGeneticNext :: Float -> Int -> [[Int]] -> [[Int]] -> SearchM [[Int]]
genGeneticNext probMutate numChildren ranges parents = do
  -- apply random changes to parents to get children
  childs <- lift $ lift $ mapM (\_ -> 
    do par1 <- randElem parents; -- choose parents
       par2 <- randElem parents;
       child <- mapM (\(idx,(g1,g2)) -> 
         do g <- randPair (g1, g2) ; -- randomly choose gene from parent
            mut <- randomRIO (0.0, 1.0); -- choose whether to mutate
            if mut <= probMutate 
            then randElem (listGet "genGeneticNext" ranges idx)
            else return g) $ zip [0..] $ zip par1 par2 ;
       return child) [1..(2*numChildren)]
  -- get unique children
  let childs' = take numChildren $ nub childs
  return childs' 

geneticVisitor1 :: Int -> SolVisitor [(SolId, Float)]
geneticVisitor1 popSize visit ranges = do
  -- create initial population
  startSids <- lift $ lift $ mapM (\_ -> randSid ranges) [1..popSize]
  -- iterate
  climbVisitor (genGeneticNext 0.2 popSize) ranges (max 2 (popSize `quot` 3)) visit startSids 

-- |Choose random parents, and randomly select genes from both, and 
-- |mutate genes with probability probMutate.
genGeneticEliteNext :: Float -> Int -> [[Int]] -> [[Int]] -> SearchM [[Int]]
genGeneticEliteNext probMutate numChildren ranges parents = do
  -- assuming first parent is best, keep as elite.
  let best = if parents == [] then error "genGeneticEliteNext:no parents!" else head parents
  -- apply random changes to parents to get children
  childs <- lift $ lift $ mapM (\_ -> 
    do par1 <- randElem parents; -- choose parents
       par2 <- randElem parents;
       child <- mapM (\(idx,(g1,g2)) -> 
         do g <- randPair (g1, g2) ; -- randomly choose gene from parent
            mut <- randomRIO (0.0, 1.0); -- choose whether to mutate
            if mut <= probMutate 
            then randElem (listGet "genGeneticNext" ranges idx)
            else return g) $ zip [0..] $ zip par1 par2 ;
       return child) [1..(2*numChildren)]
  -- get unique children (keep elitist)
  let childs' = take numChildren $ nub $ (best:childs)
  return childs' 

geneticVisitor2 :: Int -> SolVisitor [(SolId, Float)]
geneticVisitor2 popSize visit ranges = do
  -- create initial population
  startSids <- lift $ lift $ mapM (\_ -> randSid ranges) [1..popSize]
  -- iterate
  climbVisitor (genGeneticEliteNext 0.2 popSize) ranges (max 2 (popSize `quot` 3)) visit startSids 

geneticVisitor3 :: Int -> SolVisitor [(SolId, Float)]
geneticVisitor3 popSize visit ranges = do
  -- create initial population
  startSids <- lift $ lift $ mapM (\_ -> randSid ranges) [1..popSize]
  -- iterate
  climbVisitor (genGeneticEliteNext 0.1 popSize) ranges (max 2 (popSize `quot` 3)) visit startSids 

{-visitorFuns :: [(String, Int, SolVisitor [(SolId, Float)])]
visitorFuns = [
  ("depthFirst", 1, depthFirstVisitor), 
  ("reverseDepthFirst", 1, reverseDepthFirstVisitor),
  ("depthFirstBwd", 1, reverseRanges depthFirstVisitor), 
  ("reverseDepthFirstBwd", 1, reverseRanges reverseDepthFirstVisitor),
  ("greedy", 10, greedyVisitor),
  ("randomMuts1", 25, randomMutationsVisitor1),
  ("randomMuts2", 25, randomMutationsVisitor2),
  ("randomChanges1(2par,4chi,1mut)", 25, randomChangesVisitor1),
  ("randomChanges2(1par,4chi,1mut)", 25, randomChangesVisitor2),
  ("randomChanges3(1par,2chi,1mut)", 25, randomChangesVisitor3),
  ("randomChanges4(1par,3chi,1mut)", 25, randomChangesVisitor4),
  ("randomChanges5(1par,2chi,2mut)", 25, randomChangesVisitor5),
  ("randomChanges6(1par,3chi,2mut)", 25, randomChangesVisitor6),
  ("geneticVisitor1(9)", 25, geneticVisitor1 9),
  ("geneticVisitor1(8)", 25, geneticVisitor1 8),
  ("geneticVisitor1(7)", 25, geneticVisitor1 7),
  ("geneticVisitor1(6)", 25, geneticVisitor1 6),
  ("geneticVisitor1(5)", 25, geneticVisitor1 5),
  ("geneticVisitor1(4)", 25, geneticVisitor1 4),
  ("geneticVisitor1(3)", 25, geneticVisitor1 3),
  ("geneticVisitor1(2)", 25, geneticVisitor1 2)
    ]-}

visitorFuns :: [(String, Int, SolVisitor [(SolId, Float)])]
visitorFuns = [
  ("depthFirst", 1, depthFirstVisitor), 
  ("reverseDepthFirst", 1, reverseDepthFirstVisitor),
  ("depthFirstBwd", 1, reverseRanges depthFirstVisitor), 
  ("reverseDepthFirstBwd", 1, reverseRanges reverseDepthFirstVisitor),
  ("greedy", 500, greedyVisitor),
  ("greedyReverse", 500, reverseRanges greedyVisitor),
  ("randomMuts1", 500, randomMutationsVisitor1),
  ("randomMuts2", 500, randomMutationsVisitor2),
  ("randomChanges1(2par,4chi,1mut)", 500, randomChangesVisitor1),
  ("randomChanges2(1par,4chi,1mut)", 500, randomChangesVisitor2),
  ("randomChanges3(1par,2chi,1mut)", 500, randomChangesVisitor3),
  ("randomChanges4(1par,3chi,1mut)", 500, randomChangesVisitor4),
  ("randomChanges5(1par,2chi,2mut)", 500, randomChangesVisitor5),
  ("randomChanges6(1par,3chi,2mut)", 500, randomChangesVisitor6),
  ("geneticVisitor1(9)", 500, geneticVisitor1 9),
  ("geneticVisitor1(8)", 500, geneticVisitor1 8),
  ("geneticVisitor1(7)", 500, geneticVisitor1 7),
  ("geneticVisitor1(6)", 500, geneticVisitor1 6),
  ("geneticVisitor1(5)", 500, geneticVisitor1 5),
  ("geneticVisitor1(4)", 500, geneticVisitor1 4),
  ("geneticVisitor1(3)", 500, geneticVisitor1 3),
  ("geneticVisitor1(2)", 500, geneticVisitor1 2)
    ]

-- |exaustiveSearch. Starts or resumes an exaustive search. 
exaustiveSearch :: SCacheM (SolId, AvgSolCost)
exaustiveSearch = do
  ranges <- getRanges
  let spaceSz = product $ map length ranges
  --error $ (show ast) ++ "\n" ++ (show rules) ++ "\n" ++ (show ruleApps)

  -- TODO resuming a search...

  -- try all options
  t0 <- lift $ getCurrentTime
  --(sols,st) <- runStateT (visitAll getCost {-ranges []-} [] [1,3,2,2,1]) initSearchSt
  (sols,st) <- runStateT (depthFirstVisitor getCost ranges) $ initSearchSt { schSpaceSize=spaceSz }
  t1 <- lift $ getCurrentTime
  let dur = realToFrac $ diffUTCTime t1 t0
  let sols' = concat sols

  -- get info about best solution
  let best = head $ sortBy (\(_,c1) -> \(_,c2) -> compare c1 c2) sols'

  -- save results
  saveCache

  -- show results
  lift $ putStr $ "exaustively searched through " ++ (show $ schSolCount st) ++
                " solutions, taking " ++ (show $ schSolTime st) ++ "s exec time, " ++
                (show dur) ++ "s actual time.\n"

  -- return fastest
  return best

-- |Runs the search with the functions given.
trySearch :: TerminatePred -> TimeoutFun -> PrunePred -> SolVisitor [(SolId, Float)] -> SCacheM SearchSt
trySearch termPred timeFun prunePred visitor = do
  ranges <- getRanges
  let firstSid = map head ranges
  let spaceSz = product $ map length ranges
  let st0 = initSearchSt {
      schTimeout=timeFun,
      schPrune=prunePred,
      schTerminate=termPred,
      schSpaceSize=spaceSz{-,
      schBestSol=Just firstSid, -- TODO comment out later!
      schSolsVisited=DM.singleton firstSid (0,0.0)-}
    }
  st1 <- execStateT (visitor getCost ranges) st0
  return st1

-- |Show interesting search result stats as CSV.
showSearchStats :: SearchSt -> [String]
showSearchStats st = [totalIters, totalTime, (show bestTotIters), (showFFloat Nothing bestTotTime ""), bestCost] ++ sids
  where mb str = fromMaybe (error $ "showSearchStats: missing info: " ++ str)
        totalIters = show $ schSolCount st
        totalTime = showFFloat Nothing (schSolTime st) ""
        bestSid = mb "schBestSol" $ schBestSol st 
        bestCost = showFFloat Nothing (schBestCost st) ""
        (bestTotIters, bestTotTime) = mb "schSolsVisited" $ DM.lookup bestSid (schSolsVisited st)
        sids = map show bestSid

-- try Search algorithms
-- -----------------------------
-- iterations/time to converge
-- time to search end
-- how close was solution found to the global optimum?

-- |Try all combinations of search paramter functions for current search.
tryAllSearches :: SCacheM ()
tryAllSearches = do
  -- make sure exaustive search has been done to 
  -- initialize the cache
  (bestSid, bestCost) <- exaustiveSearch

  -- get all combinations of searches
  let params = [(term, tmout, prune, vis) | term <- terminatePreds, tmout <- timeoutFuns, prune <- prunePreds, vis <- visitorFuns ]
  let numParams = length params

  -- run searches
  results <- mapM (\((tn,tf),(tmn,tmf),(pn,pf),(vn,vr,vf)) -> do
      st <- trySearch tf tmf pf vf ;
      let cols = [quote vn, quote (show vr), quote tn, quote tmn, quote pn] ++ (map quote (showSearchStats st)) ;
      let line = (intercalate ", " cols) ++ "\n" ;
      lift $ putStr line  ;
      return line
    ) params

  -- csv col names
  let hdrs = ["visitor", "num repeats", "terminate", "timeout", "prune", "total iters", "total time", "iters to best", "time to best", "best cost"]
  let hdr = intercalate ", " $ map quote hdrs

  -- write CSV to file
  tm <- lift $ getCurrentTime
  dir <- gets ((fromMaybe (error "tryAllSearches: no path in search cache state!")) . scPath)
  let fn = dir ++ "/searchStats." ++ (showTime tm) ++ ".csv"
  lift $ writeFileForce fn $ hdr ++ "\n" ++ (concat results)
  lift $ putStr $ "written to: " ++ fn ++ "\n"
 
  return ()

-- |exaustiveSearch. Starts or resumes an exaustive search. 
baseSearch :: SCacheM SearchSt
baseSearch = do
  ranges <- getRanges
  let spaceSz = product $ map length ranges
  execStateT (depthFirstVisitor getCost ranges) $ initSearchSt { schSpaceSize=spaceSz }

-- |Returns time to finish, and time to find sol as a percentage of the total. Also
-- |Returns percentage time finds global optimum, and average diff between solution 's cost
-- |and global optimums.
summariseSearch :: SearchSt -> SearchSt -> [Float]
summariseSearch exSt st = [totalIters, totalTime, perIterTerm, perTimeTerm, perIterSol, perTimeSol, perBest, perDiff, foundSol]
  where mb str = fromMaybe (error $ "summariseSearch: missing info: " ++ str)
        -- from exaustive
        totalIters = realToFrac $ schSolCount exSt
        totalTime = schSolTime exSt
        bestSid = mb "exSt:schBestSol" $ schBestSol exSt 
        bestCost = schBestCost exSt
        (bestTotIters, bestTotTime) = mb "exSt:schSolsVisited" $ DM.lookup bestSid (schSolsVisited exSt)
        -- from this search
        itersTilTerm = realToFrac $ schSolCount st
        timeTilTerm = schSolTime st
        solFound = isJust $ schBestSol st
        solSid = if solFound then fromJust $ schBestSol st else [] 
        solCost = schBestCost st
        (itersTilSol, timeTilSol) = if solFound then mb "st:schSolsVisited" $ DM.lookup solSid (schSolsVisited st) else (0,0.0)
        -- stats
        foundBest = solSid == bestSid
        perBest = if foundBest then 1.0 else 0.0
        solDiff = if solCost <= 0 then bestCost else solCost - bestCost -- if all pruned so no sols, didn't find best! so diff is bestCost
        perDiff = solDiff / bestCost
        perIterTerm = (realToFrac itersTilTerm) / totalIters
        perTimeTerm = timeTilTerm / totalTime
        perIterSol = (realToFrac itersTilSol) / totalIters
        perTimeSol = timeTilSol / totalTime
        foundSol = if solFound then 1 else 0

average :: [[Float]] -> [Float]
average ll = map (/count) sums
  where count = realToFrac $ length ll
        sums = foldl1 (\a -> \b -> map (\(x,y) -> x + y) $ zip a b) ll

showSearchSummary :: [SearchSt] -> [String] -> [(String, [SearchSt])] -> [String]
showSearchSummary baseSearches nameCols results = nameCols ++ (map quote cols)
  where avgLL = map (\(baseSt, (n,l)) -> (n, map (summariseSearch baseSt) l)) $ zip baseSearches results
        avgL = concat $ map snd avgLL
        avgs = average avgL
        cols = map (\f -> showFFloat Nothing f "") avgs

-- |Try all combinations of search paramter functions for current search.
evalAllSearches :: [SCacheSt] -> IO () 
evalAllSearches caches = do
  --putStr $ show caches
  -- make sure exaustive searches have been done!
  baseSts <- mapM (evalStateT baseSearch) caches 

  -- get all combinations of searches
  let params = [(term, tmout, prune, vis) | term <- terminatePreds, tmout <- timeoutFuns, prune <- prunePreds, vis <- visitorFuns ]
  let numParams = length params

  -- run searches
  results <- mapM (\((tn,tf),(tmn,tmf),(pn,pf),(vn,vr,vf)) -> 
    do -- run this search num repeats, for all examples (caches)
       let paramCols = [quote vn, quote (show vr), quote tn, quote tmn, quote pn]
       sts <- mapM (\cache -> do res <- evalStateT (mapM (\_ -> trySearch tf tmf pf vf) [1..vr]) cache ; return (fromMaybe (error "no path!") $ scPath cache, res)) {- trace ((intercalate ", " paramCols) ++ "\n")-} caches
      
       -- output lines

       let line = showSearchSummary baseSts paramCols sts

       --let cols = [quote vn, quote (show vr), quote tn, quote tmn, quote pn] ++ (map quote (showSearchStats st)) ;
       --let line = (intercalate ", " cols) ++ "\n" ;
       --lift $ putStr line  ;
       --return line
       
       putStr $ (intercalate ", " line) ++ "\n"
       return [line]
    ) params

  -- csv col names
  let hdrs = ["visitor", "num repeats", "terminate", "timeout", "prune", "total iters", "total time", 
              "per total iters", "per total time", "per iters to sol", "per time to sol", "per find best", "avg diff", "found sol?"]
  let hdr = intercalate ", " $ map quote hdrs

  -- write CSV to file
  tm <- getCurrentTime
  let fn = "/home/taj105/searchStats." ++ (showTime tm) ++ ".csv"
  writeFileForce fn $ hdr ++ "\n" ++ (concat $ map ((++"\n") . (intercalate ", ")) $ concat results)
  putStr $ "written to: " ++ fn ++ "\n"
 
  return ()

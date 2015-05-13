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
module Compiler.Planner.SearchCache where

import Prelude hiding (catch)
import System.Directory
import Control.Exception
import System.IO.Error hiding (catch)
import Data.Maybe (fromMaybe)

import qualified Data.Map.Strict as DM
import Control.Monad.State.Strict (StateT, runStateT, evalStateT, lift, get, gets, modify)

import Compiler.Front.Common

import Compiler.Planner.Solutions
import Compiler.Planner.Rules (Ruleset)
import Compiler.Planner.SolExec (execSolution, completeSolutions, SolCtx)

data SCacheSt = SCacheSt {
    scSolCtx :: Maybe SolCtx,
    scCosts :: DM.Map SolId [SolCost],
    scMetaInfo :: DM.Map SolId SolMetaInfo,
    scCurrentSol :: Maybe [SolId],
    scPath :: Maybe String
  } deriving (Show)

emptyCacheSt = SCacheSt {
    scSolCtx = Nothing,
    scCosts = DM.empty,
    scMetaInfo = DM.empty,
    scCurrentSol = Nothing,
    scPath = Nothing
  }

type SCacheM = StateT SCacheSt IO

runWithCache :: SCacheM r -> IO r
runWithCache thunk = evalStateT thunk emptyCacheSt

setSolCtx :: SolCtx -> SCacheM ()
setSolCtx ctx = modify (\st -> st { scSolCtx=Just ctx })

getSolCtx :: SCacheM SolCtx
getSolCtx = gets $ (fromMaybe (error "SearchCache:getSolCtx: context is not set!")) . scSolCtx

clearCache :: SCacheM ()
clearCache = modify (\st -> st { scCosts=DM.empty, scMetaInfo=DM.empty, scCurrentSol=Nothing, scPath=Nothing })

-- |readOrCreateFile filePath defaultValue. Tries to open
-- |filePath and return the contents. If file doesn't exist
-- |creates it writing defaultValue to it, and returns defaultValue.
readOrCreateFile :: String -> String -> IO String
readOrCreateFile path defaultVal = do
  -- if exists
  exists <- doesFileExist path
  case exists of
    True -> do
      -- read
      val <- readFileForce path
      return val
    False -> do
      -- create file
      writeFileForce path defaultVal
      -- return default val
      return defaultVal

loadCache :: String -> SCacheM ()
loadCache path = do
  -- clear and set path
  clearCache
  modify (\st -> st { scPath=Just path })
  -- read files
  costStr <- lift $ readOrCreateFile (path ++ "/costs.txt") ""
  curStr <- lift $ readOrCreateFile (path ++ "/current.txt") $ show $ Just ([] :: SolId)
  -- deserialize
  let costs = DM.fromList $ map read $ lines costStr
  let curSol = read curStr
  -- save in state
  modify (\st -> st { scCosts=costs, scCurrentSol=curSol })
  return ()

saveCache :: SCacheM ()
saveCache = do
  -- get state
  costs <- gets scCosts
  curSol <- gets scCurrentSol
  path <- gets ((fromMaybe (error $ "saveCache: can't save, no cache path given!")) . scPath)
  -- save to new files
  let costStr = unlines $ map show $ DM.toList costs
  let curStr = show curSol
  lift $ writeFile (path ++ "/costs.new") costStr
  lift $ writeFile (path ++ "/current.new") curStr 
  -- when saved delete old
  lift $ removeFile (path ++ "/costs.txt")
  lift $ removeFile (path ++ "/current.txt") 
  -- and rename new
  lift $ renameFile (path ++ "/costs.new") (path ++ "/costs.txt")
  lift $ renameFile (path ++ "/current.new") (path ++ "/current.txt")
  return ()

getSolCost :: SolId -> SCacheM AvgSolCost
getSolCost sid = do
  lift $ putStr "entered getSolCost"
  -- lookup in cache
  costs <- gets scCosts
  case DM.lookup sid costs of
    -- cache hit
    Just cost -> do
      return $ avgCost cost
    -- cache miss
    Nothing -> do
      --return 60.0
      -- generate and time solution
      path <- gets ((fromMaybe (error $ "getSolCostCache: can't exec, no cache path given!")) . scPath)
      ctx <- gets $ (fromMaybe (error "SearchCache:getSolCost: context is not set!")) . scSolCtx
      lift $ putStr "runing execSolution"
      cost <- lift $ execSolution path ctx sid
      -- show errors
      mapM (\(i,r) -> lift $ putStr $ "getSolCost " ++ (show sid) ++ " (" ++ (show i) ++ ") returned " ++ (prettySolCost r) ++ "\n") $ zip [0..] cost
      -- add cost to map
      modify (\st -> st { scCosts=DM.insert sid cost (scCosts st) } )
      return $ avgCost cost

getSolInfo :: SolId -> SCacheM (Maybe SolMetaInfo)
getSolInfo sid = do
  -- lookup in cache
  info <- gets scMetaInfo
  case DM.lookup sid info of
    -- cache hit
    Just i -> return $ Just i
    -- cache miss
    Nothing -> do
      -- complete solution if info file doesn't exist
      path <- gets ((fromMaybe $ error "SearchCache:getSolInfo: no path in state!") . scPath)
      let fn = path ++ "/" ++ (createFilename sid) ++ ".info"
      exists <- lift $ doesFileExist fn
      r <- (case exists of 
              True -> return Nothing
              False -> return $ Just $ "no info file exists for " ++ fn {- --return Nothing -- do
                ctx <- gets $ (fromMaybe (error "SearchCache:getSolInfo: context is not set!")) . scSolCtx
                res <- lift $ evalIdxStateT 0 (completeSolutions path ctx (init sid))
                return res-})
      -- load from file
      case r of    
        Just err -> return Nothing -- error $ "SearchCache:getSolInfo: couldn't complete solution to create solution info: " ++ (show sid) ++ "\n" ++ err
        Nothing -> do
          i <- lift $ catchRetryIO (loadMetaInfo fn) 10
          return $ Just i
        




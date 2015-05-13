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

import Compiler.Front.Common
import Compiler.Front.Indices (IdxMonad)

import Compiler.Planner.SolExec
import Compiler.Planner.SearchCache
import Compiler.Planner.Searches

import Data.List (isSuffixOf, intercalate)
import qualified Data.Map.Strict as Data.Map
import qualified Data.IntMap.Strict as IM
import System.Directory
import Control.Monad.State.Strict (lift, execStateT)
import Data.Functor.Identity (runIdentity)
import Data.Maybe (isJust, isNothing)

import System.IO 
import System.Exit (exitFailure)
import Data.Time.Clock
import System.Environment (getArgs)

putStrE = hPutStr stderr

main :: IO ()
main = do
  -- get dir from command line args
  args <- getArgs 
  if (length args < 1) then error "you must specify at least one search directory!" else return ()

  -- init dirs
  let relDir = "/Compiler/Tests/PfFb/"
  curDir <- getCurrentDirectory
  let dirs = map (\subDir -> curDir ++ relDir ++ subDir) args

  -- load contexts, and caches
  caches <- mapM (\dir -> do ctx <- evalIdxStateT 0 (loadContext dir) ; cache <- execStateT (setSolCtx ctx >> loadCache dir) emptyCacheSt; return cache) dirs

  -- evaluates searches
  evalAllSearches caches

  -- display message
  putStr $ "done."
  return ()


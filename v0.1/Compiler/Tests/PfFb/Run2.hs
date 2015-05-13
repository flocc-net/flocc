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
import Control.Monad.State.Strict (lift)
import Data.Functor.Identity (runIdentity)
import Data.Maybe (isJust, isNothing)

import System.IO 
import System.Exit (exitFailure)
import Data.Time.Clock
import System.Environment (getArgs)

putStrE = hPutStr stderr

search :: String -> SCacheM String
search dir = do
  -- load cache  
  loadCache dir  

  -- do exaustive search
  tryAllSearches

  -- display result
  return ""

main2 :: IdxMonad IO ()
main2 = do
  -- get dir from command line args
  args <- lift $ getArgs 
  let subDir = (if (length args < 1) then "search7" else head args)

  -- init dir
  lift $ putStrE $ "PerformanceFeedback code gen from solution source: " ++ subDir ++ "\n"
  let relDir = "/Compiler/Tests/PfFb/" ++ subDir
  curDir <- lift $ getCurrentDirectory
  let dir = curDir ++ relDir

  -- load context 
  ctx <- loadContext dir

  -- run with cache
  msg <- lift $ runWithCache (setSolCtx ctx >> search dir)

  -- display message
  lift $ putStr $ msg

  return ()

main :: IO ()
main = do
  evalIdxStateT 0 main2
  return ()

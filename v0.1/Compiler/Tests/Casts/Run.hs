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

import Compiler.Front.Front
import Compiler.Front.ExprTree

import Compiler.Types2.TypeAssignment (showExprWithTypes)

import Compiler.Planner.SolExec
import Compiler.Planner.InsertCasts

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
import System.Timeout (timeout)

-- Tries to fix a program with broken constraints
-- by inserting type casts/redistribution function
-- applications

main2 :: IdxMonad IO ()
main2 = do
  -- get dir from command line args
  args <- lift $ getArgs 
  let subDir = (if (length args < 1) then "" else head args)
 
  -- init dir
  lift $ putStrE $ "Automatic cast insertion test " ++ subDir ++ "\n"
  let relDir = "/Compiler/Tests/Casts/" ++ subDir
  curDir <- lift $ getCurrentDirectory
  let dir = curDir ++ relDir

  -- load context 
  ctx <- loadContext dir
  let varIds = ctxVarIdMap ctx
  let varTys = ctxVarTyMap ctx

  -- parse input program
  let libSrc = ctxLibSrc ctx
  src1 <- lift $ readFileForce $ dir ++ "/" ++ "mandel2.flocc"
  ast1 <- parseSrc (ctxVarIds ctx) ({-libSrc ++-} src1)

  -- try and insert casts
  t0 <- lift $ getCurrentTime
  (sols, dbgMsg) <- findCasts varTys varIds ast1
  t1 <- lift $ getCurrentTime
  let curDur = realToFrac $ diffUTCTime t1 t0

  -- display solutions
  lift $ putStr $ intercalate "\n\n" $ map (\(ast,tys,cost) -> (show cost) ++ ":\n" ++ (showP ast)) $ reverse sols
  --lift $ putStr $ intercalate "\n\n" $ map (\(ast,tys,cost) -> (show cost) ++ ":\n" ++ (showExprWithTypes tys ast)) $ reverse sols
  lift $ putStr "\n"
  lift $ putStr $ (show curDur) ++ "s\n"
  return ()

main :: IO ()
main = do
  evalIdxStateT 0 main2
  return ()

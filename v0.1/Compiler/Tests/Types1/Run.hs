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

import Compiler.Types.Types
import Compiler.Types.TypeAssignment

import Data.List (isSuffixOf)
import System.Directory

main :: IO ()
main = do
  -- get test suite dir
  curDir <- getCurrentDirectory
  let testDir = curDir ++ "/Compiler/Tests/Types1/"

  -- show caption
  putStr $ "Types1: Load type defs in: " ++ testDir ++ "\n"

  -- get directory listing type def files
  contents <- getDirectoryContents testDir
  let typeFiles = filter (isSuffixOf ".types") contents
  let typePaths = map (testDir++) typeFiles
 
  -- try and parse them all, catching any exceptions
  typeDefs <- evalIdxStateT 0 (mapM loadTypes typePaths)

  -- show types
  mapM (\(p,d) -> do putStr (show p) ; putStr "\n--------------\n" ; putStr (show d) ; putStr "\n") $ zip typeFiles typeDefs

  putStr "\n\n"

  return ()

  

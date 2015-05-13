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

import System.Directory
import Data.List (isSuffixOf)

import Compiler.Front.Front
import Compiler.Front.ExprTree
import Compiler.Front.SrcLexer
import Compiler.Front.SrcParser

main :: IO ()
main = do
  -- get test suite path
  curDir <- getCurrentDirectory
  let testDir = curDir ++ "/Compiler/Tests/FrontEnd1/"

  -- show caption
  putStr $ "FrontEnd1: Parse input programs in: " ++ testDir ++ "\n"

  -- get directory listing flocc programs
  contents <- getDirectoryContents testDir
  let floccFiles = filter (isSuffixOf ".flocc") contents
  let floccPaths = map (testDir++) floccFiles
 
  -- read in each flocc program
  srcPrograms <- mapM readFile floccPaths

  -- try and parse them all, catching any exceptions
  asts <- mapM testParseSrcFile floccPaths

  -- show results
  mapM (\(path,code,ast) -> do putStr "\n----------------\n" ; 
                               putStr path ; 
                               putStr "\n----------------\n" ; 
                               putStr code ; 
                               putStr "----------------\n" ; 
                               putStr (show ast)) $ zip3 floccFiles srcPrograms asts

  putStr "\n\n"
  return ()

-- parse source code
 {- pg <- parseAndLabel typeNames (scan s)
  --pg <- parseAndLabel (flipAssocList globalNames) (scan s)
  --pg <- generateGraph 
  pg' <- convertAllToLets pg
  pg'' <- applyLetLifting pg'
-}

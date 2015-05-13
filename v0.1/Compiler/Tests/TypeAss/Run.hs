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
import Compiler.Front.SrcLexer
import Compiler.Front.SrcParser

import Compiler.Types.Types
import Compiler.Types.TypeAssignment (assignTypes, showExprWithTypes)

import Data.List (isSuffixOf)
import System.Directory
import Control.Monad.State.Strict (lift)

main2 :: IdxMonad IO ()
main2 = do
  lift $ putStr "Type assignment:\n"  

  -- load types
  curDir <- lift $ getCurrentDirectory
  let typesPath = curDir ++ "/Compiler/Tests/TypeAss/lib1.types"
  lift $ putStr $ "Load type defs from: " ++ typesPath ++ "\n"
  (varIds, typeDefs) <- loadTypes typesPath -- varIds maps var names to idxs, typeDefs maps var ids to type schemes

  -- load source file
  let testFile = curDir ++ "/Compiler/Tests/TypeAss/program1.flocc"
  ast <- parseSrcFile varIds testFile

  -- perform type assignment
  astTypes <- assignTypes typeDefs ast
  lift $ putStr "Success:\n"
  lift $ putStr $ showExprWithTypes astTypes ast

  lift $ putStr "\n\n"
  return ()

main :: IO ()
main = do
  evalIdxStateT 0 main2
  return ()

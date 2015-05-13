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
import Compiler.Front.Preprocess

import Compiler.Types.Types
import Compiler.Types.TypeAssignment (assignTypes, showExprWithTypes)

import Compiler.Back.FromFront
import Compiler.Back.Graph (showSubgraphs)
import Compiler.Back.GraphBuilder
import Compiler.Back.ShowGraph (dotDraw)
import Compiler.Back.Gen
import Compiler.Back.Generators

import Compiler.Tests.BackEnd1.HistTemplates
import Compiler.Tests.BackEnd1.NodeLayouts (declareNodeLayouts)

import Data.List (isSuffixOf)
import qualified Data.Map.Strict as Data.Map
import qualified Data.IntMap.Strict as IM
import System.Directory
import Control.Monad.State.Strict (lift)
import Data.Functor.Identity (runIdentity)

main2 :: IdxMonad IO ()
main2 = do
  lift $ putStr "BackEnd1 code gen from solution source:\n"  
  let relDir = "/Compiler/Tests/BackEnd1/"

  -- load types
  curDir <- lift $ getCurrentDirectory
  let typesPath = curDir ++ relDir ++ "lib1.types"
  lift $ putStr $ "Load type defs from: " ++ typesPath ++ "..."
  (varIds, typeDefs) <- loadTypes typesPath -- varIds maps var names to idxs, typeDefs maps var ids to type schemes
  lift $ putStr "Done.\n"

  -- load flocc library
  libSrc <- lift $ readFile $ curDir ++ "/lib1.flocc"

  -- load source file
  let testFile = curDir ++ relDir ++ "program1.flocc"
  progSrc <- lift $ readFile testFile
  let src = libSrc ++ progSrc
  ast <- parseSrc varIds src

  -- preprocess source
  lift $ putStr "Preprocessing AST..."
  ast' <- preprocessExpr varIds ast
  lift $ putStr $ show ast'
  lift $ putStr "Success.\n"

  -- perform type assignment
  lift $ putStr "Inferring program types..."
  astTypes <- assignTypes typeDefs ast'
  lift $ putStr "Success.\n"
  lift $ putStr $ showExprWithTypes astTypes ast'

  -- encapsulate all paramter functions in lambdas
  -- for the back end
  lift $ putStr "\n\nEncapsullating parameter funs in lambdas..."
  (ast'', astTypes') <- encapFunVars astTypes ast' 
  lift $ putStr "Success.\n"
  lift $ putStr $ show ast''
  lift $ putStr $ showExprWithTypes astTypes' ast''

  -- translate into back end types
  lift $ putStr "Translating into backend types..."
  let astTypes'' = translateTyEnv astTypes'
  lift $ putStr $ show astTypes''
  lift $ putStr "Done.\n"

  -- generate data flow graph...
  lift $ putStr "Building DFG from AST..."
  (graph, graphTypes) <- graphFromExpr astTypes'' ast''
  lift $ putStr $ dotDraw graph
  lift $ putStr $ "\n\n"
  lift $ putStr $ showSubgraphs graph
  lift $ putStr "Done.\n"

  -- generate target code
  lift $ putStr "Generating target code..."
  let generators' = Data.Map.fromList generators
  let templates' = Data.Map.fromList templates
  let outStreams = runIdentity $ generate (declareNodeLayouts $ IM.elems graphTypes) generators' templates' graphTypes graph 1
  libCode <- lift $ readFile $ curDir ++ relDir ++ "mpiLib.cpp"
  lift $ putStr libCode
  case Data.Map.lookup "decls" outStreams of
    Just str -> do
      lift $ putStr str
      lift $ putStr "\n\n"
      return ()
    Nothing  -> lift $ putStr "// No stream called 'decls' found in output streams.\n"
  lift $ putStr "void run() {"
  case Data.Map.lookup "init" outStreams of
    Just str -> do
      lift $ putStr str
      return ()
    Nothing  -> lift $ putStr "// No stream called 'init' found in output streams.\n"
  case Data.Map.lookup "main" outStreams of
    Just str -> do
      lift $ putStr str
      return ()
    Nothing  -> lift $ putStr "// No stream called 'main' found in output streams.\n"
  case Data.Map.lookup "final" outStreams of
    Just str -> do
      lift $ putStr str
      return ()
    Nothing  -> lift $ putStr "// No stream called 'final' found in output streams.\n"
  lift $ putStr "}\n\n"
  mainCode <- lift $ readFile $ curDir ++ relDir ++ "histMain.cpp"
  lift $ putStr mainCode
  lift $ putStr "//\n\n"

  lift $ putStr "\n\n"
  return ()

main :: IO ()
main = do
  evalIdxStateT 0 main2
  return ()

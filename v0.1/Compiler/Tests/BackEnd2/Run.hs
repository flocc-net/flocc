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
import Compiler.Types.TermLanguage (Term(..), FunctionToken(Tok), Scheme(..))
import Compiler.Types.TypeAssignment (assignTypes, showExprWithTypes, TyToken(Ty))
import Compiler.Types.DepTypeAssignment (assignDepTypes, showExprWithDepTypes)
import Compiler.Types.EmbeddedFunctions (simplifyFunsInEnv, fullySimplifyFun)
import Compiler.Types.FillGaps
import Compiler.Types.Solver (fillGapsInEnv)

import Compiler.Back.FromFront2
import Compiler.Back.Graph (showSubgraphs)
import Compiler.Back.GraphBuilder
import Compiler.Back.ShowGraph (dotDraw)
import Compiler.Back.Gen
import Compiler.Back.Generators

import Compiler.Tests.BackEnd2.ArrTemplates

import Data.List (isSuffixOf, intercalate)
import qualified Data.Map.Strict as Data.Map
import qualified Data.IntMap.Strict as IM
import System.Directory
import Control.Monad.State.Strict (lift)
import Data.Functor.Identity (runIdentity)

main2 :: IdxMonad IO ()
main2 = do
  lift $ putStr "BackEnd2 code gen from solution source:\n"  
  let relDir = "/Compiler/Tests/BackEnd2/"

  -- load types
  curDir <- lift $ getCurrentDirectory
  let typesPath = curDir ++ relDir ++ "lib1.types"
  lift $ putStr $ "Load type defs from: " ++ typesPath ++ "..."
  (varIds, typeDefs) <- loadDepTypes typesPath -- varIds maps var names to idxs, typeDefs maps var ids to type schemes
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
  {-lift $ putStr "Inferring program types..."
  astTypes <- assignDepTypes (IM.fromList typeDefs) ast'
  lift $ putStr "Success.\n"
  lift $ putStr $ showExprWithDepTypes astTypes ast'-}

  -- TODO FIX SO FILTERS OUT SOLUTIONS THAT MEAN GENERATORS
  -- CAN'T RUN.

  -- perform type assignment & make choices as we go...
  lift $ putStr "Inferring program types..."
  astTypes <- findSolutions (IM.fromList typeDefs) ast'
  lift $ putStr "Success.\n"
  lift $ putStr $ intercalate "\n" $ map (\env -> showExprWithDepTypes (map (\(i,t) -> (i, Scheme [] t)) $ IM.toList env) ast') astTypes

  -- get first solution
  let astTypes' = last astTypes 

  -- run fill gaps...
  {-let astTypes1 = head astTypes
  gapFillers <- fillGapsInEnv astTypes1
  lift $ putStr $ "\n\nFillGaps:\n\n" ++ (intercalate ",\n" $ map show $ IM.toList gapFillers)-}

  -- simplify all functions that are embedded
  -- in the types
  {-lift $ putStr "\n\nSimplifying functions embedded in types..."
  astTypes' <- simplifyFunsInEnv astTypes
  lift $ putStr "Done.\n"
  --t' <- simplifyFun (Term (Tok (Ty "FFst")) [])
  --lift $ putStr $ show t'
  --lift $ putStr $ showExprWithTypes astTypes' ast'
  lift $ putStr $ showExprWithDepTypes astTypes' ast'-}

  -- TODO infer integer domains

  -- encapsulate all paramter functions in lambdas
  -- for the back end
  lift $ putStr "\n\nEncapsullating parameter funs in lambdas..."
  (ast'', astTypes'') <- encapFunVars (IM.toList $ IM.map (\t -> Scheme [] t) astTypes') ast' 
  lift $ putStr "Success.\n"
  lift $ putStr $ show ast''
  lift $ putStr $ showExprWithTypes astTypes'' ast''

  -- TODO convert to back end types, including converting
  -- embedded funs to graphs -}

  -- make exp map
  let expEnv = IM.fromList $ makeExprMap ast'

  -- translate into back end types
  lift $ putStr "\n\nTranslating into backend types..."
  astTypes''' <- translateTypes expEnv (IM.fromList typeDefs) (IM.map (\(Scheme [] t) -> t) $ IM.fromList astTypes'')
  lift $ putStr $ show astTypes'''
  lift $ putStr "Done.\n"

--translateTypes :: Monad m => IM.IntMap E.Expr -> IM.IntMap F.TySchemeEx -> IM.IntMap F.TyTerm -> IdxMonad m (IM.IntMap B.Ty)
--translateTypes expEnv varTypes expTypes = do

  -- generate data flow graph...
  lift $ putStr "\nBuilding DFG from AST..."
  (graph, graphTypes) <- graphFromExpr astTypes''' ast''
  lift $ putStr $ dotDraw graph
  lift $ putStr $ "\n\n"
  lift $ putStr $ showSubgraphs graph
  lift $ putStr "Done.\n"

  -- generate target code
  lift $ putStr "Generating target code..."
  let generators' = Data.Map.fromList generators
  let templates' = Data.Map.fromList templates
  let outStreams = runIdentity $ generate (return ()) generators' templates' graphTypes graph 1
  --libCode <- lift $ readFile $ curDir ++ relDir ++ "mpiLib.cpp"
  --lift $ putStr libCode
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
  --mainCode <- lift $ readFile $ curDir ++ relDir ++ "histMain.cpp"
  --lift $ putStr mainCode
  lift $ putStr "//\n\n"

  lift $ putStr "\n\n"
  return ()

main :: IO ()
main = do
  evalIdxStateT 0 main2
  return ()

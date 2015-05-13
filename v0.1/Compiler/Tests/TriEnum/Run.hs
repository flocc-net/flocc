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
import Compiler.Types.FillGaps (possibleSubs, remRedundantDims)
import Compiler.Types.Solver (fillGapsInEnv)

import Compiler.Back.FromFront2
import Compiler.Back.Graph (showSubgraphs)
import Compiler.Back.GraphBuilder
import Compiler.Back.ShowGraph (dotDraw)
import Compiler.Back.Gen
import Compiler.Back.Generators
import Compiler.Back.CartTopology (initNodeCoordArr)

import Compiler.Tests.TriEnum.Templates

import Data.List (isSuffixOf, intercalate)
import qualified Data.Map.Strict as Data.Map
import qualified Data.IntMap.Strict as IM
import System.Directory
import Control.Monad.State.Strict (lift)
import Data.Functor.Identity (runIdentity)

import System.IO 
import System.Exit (exitFailure)

putStrE = hPutStr stderr

main2 :: IdxMonad IO ()
main2 = do
  lift $ putStrE "TriEnum code gen from solution source:\n"  
  let relDir = "/Compiler/Tests/TriEnum/"

  -- load types
  curDir <- lift $ getCurrentDirectory
  let typesPath = curDir ++ relDir ++ "lib1.types"
  lift $ putStrE $ "Load type defs from: " ++ typesPath ++ "..."
  (varIds, typeDefs) <- loadDepTypes typesPath -- varIds maps var names to idxs, typeDefs maps var ids to type schemes
  lift $ putStrE "Done.\n"

  -- load flocc library
  libSrc <- lift $ readFile $ curDir ++ "/lib1.flocc"

  -- load source file
  let testFile = curDir ++ relDir ++ "program1.flocc"
  progSrc <- lift $ readFile testFile
  let src = libSrc ++ progSrc
  ast <- parseSrc varIds src

  -- preprocess source
  lift $ putStrE "Preprocessing AST..."
  ast' <- preprocessExpr varIds ast
  lift $ putStrE $ show ast'
  lift $ putStrE "Success.\n"

  -- perform type assignment
  {-lift $ putStrE "Inferring program types..."
  astTypes <- assignDepTypes (IM.fromList typeDefs) ast'
  lift $ putStrE "Success.\n"
  lift $ putStrE $ showExprWithDepTypes astTypes ast'-}

  -- TODO FIX SO FILTERS OUT SOLUTIONS THAT MEAN GENERATORS
  -- CAN'T RUN.

  -- perform type assignment & make choices as we go...
  lift $ putStrE "Inferring program types..."
  astTypes <- findSolutions (IM.fromList typeDefs) ast'
  lift $ putStrE "Success.\n"
  lift $ putStrE $ intercalate "\n" $ map (\env -> showExprWithDepTypes (map (\(i,t) -> (i, Scheme [] t)) $ IM.toList env) ast') astTypes

  -- get first solution
  let astTypes' = last astTypes 

  -- run fill gaps...
  {-let astTypes1 = head astTypes
  gapFillers <- fillGapsInEnv astTypes1
  lift $ putStrE $ "\n\nFillGaps:\n\n" ++ (intercalate ",\n" $ map show $ IM.toList gapFillers)-}

  -- simplify all functions that are embedded
  -- in the types
  {-lift $ putStrE "\n\nSimplifying functions embedded in types..."
  astTypes' <- simplifyFunsInEnv astTypes
  lift $ putStrE "Done.\n"
  --t' <- simplifyFun (Term (Tok (Ty "FFst")) [])
  --lift $ putStrE $ show t'
  --lift $ putStrE $ showExprWithTypes astTypes' ast'
  lift $ putStrE $ showExprWithDepTypes astTypes' ast'-}

  -- TODO infer integer domains

  -- encapsulate all paramter functions in lambdas
  -- for the back end
  lift $ putStrE "\n\nEncapsullating parameter funs in lambdas..."
  (ast'', astTypes1'') <- encapFunVars (IM.toList $ IM.map (\t -> Scheme [] t) astTypes') ast' 
  lift $ putStrE "Success.\n"
  lift $ putStrE $ show ast''
  lift $ putStrE $ showExprWithTypes astTypes1'' ast''

  -- TODO convert to back end types, including converting
  -- embedded funs to graphs -}

  -- remove redundant mirror dims
  let astTypes'' = IM.toList $ IM.map (\t -> Scheme [] t) $ remRedundantDims $ IM.map (\(Scheme [] t) -> t) $ IM.fromList astTypes1''
  lift $ putStrE $ showExprWithTypes astTypes'' ast''
  --error "bla"

  -- make exp map
  let expEnv = IM.fromList $ makeExprMap ast'
  --lift $ exitFailure

  -- translate into back end types
  lift $ putStrE "\n\nTranslating into backend types..."
  astTypes''' <- translateTypes expEnv (IM.fromList typeDefs) (IM.map (\(Scheme [] t) -> t) $ IM.fromList astTypes'')
  lift $ putStrE $ show astTypes'''
  lift $ putStrE "Done.\n"

--translateTypes :: Monad m => IM.IntMap E.Expr -> IM.IntMap F.TySchemeEx -> IM.IntMap F.TyTerm -> IdxMonad m (IM.IntMap B.Ty)
--translateTypes expEnv varTypes expTypes = do

  -- generate data flow graph...
  lift $ putStrE "\nBuilding DFG from AST..."
  (graph, graphTypes) <- graphFromExpr astTypes''' ast''
  lift $ putStrE $ dotDraw graph
  lift $ putStrE $ "\n\n"
  lift $ putStrE $ showSubgraphs graph
  lift $ putStrE "Done.\n"

  -- generate target code
  lift $ putStrE "Generating target code..."
  let generators' = Data.Map.fromList generators
  let templates' = Data.Map.fromList templates
--   let outStreams = runIdentity $ generate (return ()) generators' templates' graphTypes graph 1
  let outStreams = runIdentity $ generate initNodeCoordArr generators' templates' graphTypes graph 1
  libCode <- lift $ readFile $ curDir ++ relDir ++ "header.h"
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
  mainCode <- lift $ readFile $ curDir ++ relDir ++ "main.cpp"
  lift $ putStr mainCode
  lift $ putStr "//\n\n"

  lift $ putStr "\n\n"
  return ()

main :: IO ()
main = do
  evalIdxStateT 0 main2
  return ()

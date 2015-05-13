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
module Compiler.Back.Back where

import qualified Data.Map.Strict as DM
import qualified Data.IntMap.Strict as IM
import Data.Maybe (fromMaybe)
import Data.Functor.Identity (runIdentity)
import Control.Monad.Catch

import Compiler.Front.Indices (IdxMonad)
import Compiler.Front.Common (ShowP(..))
import Compiler.Front.ExprTree (Expr, makeExprMap)

import Compiler.Types2.TermLanguage
import Compiler.Types2.TypeAssignment

import Compiler.Back.FromFront2
import Compiler.Back.GraphBuilder
import Compiler.Back.Generators
import qualified Compiler.Back.Gen as G
import Compiler.Back.AllTemplates (templates)
import Compiler.Back.CartTopology
import Compiler.Back.ShowGraph

-- |generate varTypes astTypes ast. Generates C++ and MPI code that implements 
-- |ast, where varTypes has library function types, and astTypes has the types of 
-- |the ast subexpressions.
generate :: (MonadCatch m, Monad m) => IM.IntMap TySchemeEx -> IM.IntMap TyTerm -> Expr -> IdxMonad m (String, String)
generate types astTypes ast = do
  -- convert types to backend types
  let expEnv = IM.fromList $ makeExprMap ast
  astTypes <- translateTypes expEnv types astTypes
  -- generate DFG
  --error $ "input graph: \n" ++ (showP ast) ++ "\n\n"
  (graph, graphTypes) <- graphFromExpr astTypes ast
  -- show dot DFG
  --error $ dotDraw graph
  -- generate target code
  let generators' = DM.fromList generators
  let templates' = DM.fromList templates
  outStreams <- G.generate initNodeCoordArr generators' templates' graphTypes graph 1
  -- assemble code blocks
  let decls = fromMaybe "// No stream called 'decls' found in output streams.\n" $ DM.lookup "decls" outStreams
  let globals = fromMaybe "// No stream called 'globals' found in output streams.\n" $ DM.lookup "globals" outStreams
  let funs = fromMaybe "// No stream called 'funs' found in output streams.\n" $ DM.lookup "funs" outStreams
  let init = fromMaybe "// No stream called 'init' found in output streams.\n" $ DM.lookup "init" outStreams
  let main = fromMaybe "// No stream called 'main' found in output streams.\n" $ DM.lookup "main" outStreams
  let final = fromMaybe "// No stream called 'final' found in output streams.\n" $ DM.lookup "final" outStreams
  let code = "// declarations\n" ++ decls ++
             "// global vars\n" ++ globals ++
             "// functiions\n" ++ funs ++ 
             "\nvoid run() {\n" ++ 
               "  // init\n" ++ init ++ 
               "  // main\n" ++ main ++
               "  // final\n" ++ final ++
             "\n}\n\n"
  -- return 
  return (code, dotDraw graph)



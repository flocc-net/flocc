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
module Compiler.Types.Types where

import Compiler.Front.Indices
import Compiler.Front.ExprTree

import Compiler.Types.TypeLexer
import Compiler.Types.TypeParser
import Compiler.Types.TermLanguage (emptyTermEnv)
import Compiler.Types.TermBuilder
import qualified Compiler.Types.TypeAssignment as TA
import Compiler.Types.TypeAssignment

import Compiler.Types.Builder
import Compiler.Types.Solver

import qualified Data.IntMap.Strict as IM
import Control.Monad.State.Strict (lift, runStateT)

-- |loadTypes path. Reads the type def file at path, and returns a map
-- |from var names to idxs, and a map from idxs to type schemes.
loadTypes :: FilePath -> IdxMonad IO ([(String, Idx)], [(Idx, TyScheme)])
loadTypes path = do
  -- read in file
  src <- lift $ readFile path
  -- lex and parse it
  typeDecs <- parseTypes src
  -- make environments from def list
  typeList <- numberTypes typeDecs
  let namesToNums = typeNameMap typeList
  let idxsToSchemes = typeEnv typeList
  return (namesToNums, idxsToSchemes)

-- |loadDepTypes path. Reads the type def file at path, and returns a map
-- |from var names to idxs, and a map from idxs to dependent type schemes. 
loadDepTypes :: FilePath -> IdxMonad IO ([(String, Idx)], [(Idx, TySchemeEx)])
loadDepTypes path = do
  -- read in file
  src <- lift $ readFile path
  -- lex and parse it
  typeDecs <- parseTypes src
  -- make environments from def list
  typeList <- numberTypes typeDecs
  let namesToNums = typeNameMap typeList
  let idxsToSchemes = typeDecsToSchemeExEnv typeList
  return (namesToNums, idxsToSchemes)

findSolutions :: Monad m => VarMap TySchemeEx -> Expr -> IdxMonad m [TmEnv]
findSolutions varEnv expr = do
  -- create constraints
  ((cl,_),tyEnv) <- runStateT (buildConstrs varEnv IM.empty expr) emptyTermEnv
  -- check constraints
  let cl' = checkConstraints cl
  -- solve constrs
  solutions <- solve (varMapFromSchemeEnv tyEnv) emptySubs cl'
  -- apply subs to env as required by solve
  let envs = map (\(choice, subs, env) -> mapEnv (applySubsToTm subs) env) solutions 
  return envs

--type TyEnv = [(Idx, TyScheme)]
{-inferTypes :: Monad m => TyEnv -> Expr -> IdxMonad m (Either TyEnv String)
inferTypes varTypes ast = do
  res <- runTermInferencer TA.inferTypes varTypes ast
  case res of
    Left types -> return $ Left types
    Right const -> return $ Right $ "Constraint failed: " ++ (show const)
-}
-- TODO make TyEnv an IntMap.Strict

-- let globalTypes = typeDecsToSchemeExEnv typeList
-- let types' = map (\(i, SchemeEx it (Scheme l t)) -> (i, Scheme (l++(getIdsInIdTree it)) t)) globalTypes


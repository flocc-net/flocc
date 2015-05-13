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
module Compiler.Tests.BackEnd1.NodeLayouts where

import Compiler.Back.Graph
import Compiler.Back.GenDecls
import Compiler.Back.Gen
import Compiler.Back.StrTemplates

import Data.Set (Set)
import qualified Data.Set (toList, fromList)

-- |Equivalent to global communicator
allNodesTy :: Ty
allNodesTy = (Lf (LfTy "AllNodes" []))

getLayoutVar :: Monad m => Ty -> GenM1 m (Maybe (Val m)) 
getLayoutVar nsTy = do
  maybeVar <- getGlobal "nodeLayouts" (Lf $ TyOV nsTy)
  return maybeVar

-- |getNodeSetVar nsVarName nsTy. Queries the globals to find the 
-- |nodeset var associated with nsTy, and binds it to nsVarName
-- |in the local environment. 
getNodeSetVar :: Monad m => Id -> Ty -> GenM m
getNodeSetVar destName nsTy = do
  -- get var
  maybeVar <- getLayoutVar nsTy
  -- if found
  case maybeVar of
    Just var -> do -- bind it to the local var
      setLocalVal destName var
      return ()
    Nothing  -> do -- error
      let errMsg = "getNodeSetVar: no nodeSet var exists for " ++ (show nsTy)
      genError errMsg
      return $ error errMsg

-- |layoutTyPositions. Offsets (base 0) into
-- |LfTy parameter lists of node layouts.
layoutTyPositions = [
  ("DistVec", 3),
  ("DistArr1D", 3),
  ("DistMap", 4)
  ]

-- |findLayoutInType lfTy. Searches through all layoutTyPositions
-- |to see if any matches this type. If one does, returns the 
-- |nodeLayout type at the offset given.
findLayoutInType :: LfTy -> [Ty]
findLayoutInType (LfTy name l) = 
  (concat $ map (\(n,idx) -> if name == n then [l !! idx] else []) layoutTyPositions) ++
  (concat $ map (searchTree findLayoutInType) l)
findLayoutInType _ = []

declareNodeLayout :: Monad m => Ty -> GenM m
declareNodeLayout ty = do
  -- make a new name for it
  vid <- newInt
  let vname = "nl" ++ (show vid)
  -- generate var declaration, in decls
  output "decls" $ "NodeLayout " ++ vname ++ ";\n"
  -- save varname in globals under ty
  setGlobal "nodeLayouts" (Lf $ TyOV ty) (Just $ VarV (Lf $ LfTy "NodeLayout" []) (Lf vname))
  case ty of 
    -- global node layout
    (Lf (LfTy "AllNodes" [])) -> do
      -- generate init code, in main
      output "main" $ applyT decNodeLayoutTem [("nl", vname)] 
      -- generate finalize code
      output "final" $ applyT "<nl>.Free();\n" [("nl", vname)] 
      -- for allNodes assign to allNodes too
      output "main" $ "allNodes = " ++ vname ++ ";\n"
    -- any other
    other -> error $ "NodeLayouts:declareNodeLayout: not implemented, can't generate init code for " ++ (show other)

decNodeLayoutTem =   "  <nl>.partitionCom = &MPI::COMM_WORLD;\n\
\  <nl>.partitionCount = MPI::COMM_WORLD.Get_size();\n\
\  <nl>.partitionRank = MPI::COMM_WORLD.Get_rank();\n\
\  <nl>.mirrorCom = NULL;\n\
\  <nl>.mirrorCount = 1;\n\
\  <nl>.mirrorRank = 0;\n\
\  <nl>.mirrorRootRank = 0;\n"

-- |declareNodeLayouts types. Analyses all types, looking for
-- |node layouts, and creating declarations for each of them,
-- |and binding their names in the "nodeLayouts" globals map.
declareNodeLayouts :: Monad m => [Ty] -> GenM m
declareNodeLayouts types = do
  -- find node layouts in types
  let layoutList = concat $ map (searchTree findLayoutInType) types
  -- find unique ones
  let layoutSet = Data.Set.fromList layoutList
  -- for each, declare it and reference it in globals "nodeLayouts"
  output "decls" "// declaring node layouts\n"
  output "main" "  // initializing node layouts\n"
  mapM declareNodeLayout $ Data.Set.toList layoutSet 
  output "decls" "\n\n"
  output "main" "\n\n"
  return () 

-- TODO need to break down into tree with common var root nodes
-- then choose size for each leaf dimension, and create node layouts
-- for every node/type in the tree.


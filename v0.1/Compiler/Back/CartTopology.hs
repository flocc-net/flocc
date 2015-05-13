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
module Compiler.Back.CartTopology where

import Compiler.Front.Common (listGet)
import qualified Compiler.Types2.TypeInfo as F

import Compiler.Back.Graph
import Compiler.Back.GenDecls
import Compiler.Back.Gen
import Compiler.Back.Generators

import Control.Monad.State.Strict (gets, modify)
import Control.Monad.Catch
import Data.Maybe (fromMaybe)
import qualified Data.Set as DS
import qualified Data.IntMap as IM
import qualified Data.Map as DM
import qualified Data.List as DL

-- |getDimIdsFromLfTy ty. Returns all the var ids of dims in DMaps and DArrs in ty.
getDimIdsFromLfTy :: LfTy -> DS.Set String
getDimIdsFromLfTy (LfTy n l) = dimTys
  where dimL = F.dimLocs n
        dimTys = DS.unions $ map (\i -> getVarsInTy $ listGet "CartTop:getDimIdsFromLfTy" l i) dimL
getDimIdsFromLfTy other = error $ "CartTop:getDimIdsFromLfTy: " ++ (show other)
{-case (n,l) of
  --("DMap", [mode, keyT, valT, ordF, parF, parD, mirD]) -> (getVarsInTy parD) `DS.union` (getVarsInTy mirD)
  --("DArr", [mode, idxT, valT, layF, parF, parD, mirD]) -> (getVarsInTy parD) `DS.union` (getVarsInTy mirD)
  other  -> DS.unions $ map getDimIdsFromTy l-}

-- |getDimIdsFromTy ty. Returns all the var ids of dims in DMaps and DArrs in ty.
getDimIdsFromTy :: Ty -> DS.Set String
getDimIdsFromTy ty = DS.unions $ map getDimIdsFromLfTy $ treeToList ty

initNodeRanks :: Monad m => Id -> Id -> [Int] -> [(Int,Int)] -> GenM1 m Code
initNodeRanks mapVid commVid dims [] = -- code in inner loop
  return $ mapVid ++ (concat $ map (\d -> "[coord[" ++ (show d) ++ "]]") dims) ++ " = " ++ commVid ++ ".Get_cart_rank(coord);\n" 
initNodeRanks mapVid commVid dims ((globDim,locDim):remDims) = do
  let d = show locDim
  inner <- initNodeRanks mapVid commVid dims remDims
  return $ "for (coord[" ++ d ++ "] = 0; coord["++d++"] < dimSizes["++(show globDim)++"]; coord[" ++ d ++ "]++) {\n" ++ inner ++ "}\n"

-- |initNodeCoordArr. Generates code to create a cartesian topology for COMM_WORLD
-- |with the right num of dims (trying to keep dim lengths roughly equal)
-- |and inits an array of node coords to ranks using it.
initNodeCoordArr :: Monad m => GenM m
initNodeCoordArr = do
  -- get the dim names (sorted list)
  tyEnv <- gets (globTypes.genConsts)
  let types = IM.elems tyEnv 
  let dimNames = DS.toAscList $ DS.unions $ map getDimIdsFromTy types 
  let ndims = show $ length dimNames
  -- save dim ids in generator state
  let dimNamesToInts = DM.fromList $ map (\(n,i) -> (Lf $ IdOV n, LitV $ IntVal i)) $ zip dimNames [0..]
  modify (\st -> st { genGlobals=DM.insert "dimNamesToInts" dimNamesToInts (genGlobals st)} )
  modify (\st -> st { genGlobals=DM.insert "subCarts" DM.empty (genGlobals st)} )
  -- create declarations of global vars
  let decls = "\n// Global cartesian communicator\n"++
              "static const int ndims = " ++ ndims ++ ";\n"++
              "static const int maxNodesPerDim = 4096;\n"++
              "static std::vector<int> dimSizes;\n" ++
              "static MPI::Cartcomm cartComm;\n"++
              "static int coordRanks" ++ (concat $ replicate (length dimNames) "[maxNodesPerDim]") ++ ";\n"++
              "static int thisCoord[ndims];\n"++
              "static int thisRank, Nproc, rootRank;\n\n\n"
  -- create code to choose sizes for each
  let initCode = "thisRank = MPI::COMM_WORLD.Get_rank();\n" ++
                 "Nproc = MPI::COMM_WORLD.Get_size();\n"++
                 "dimSizes = flocc::findBestDims(Nproc, ndims);\n"
  -- create cart topology code 
  let cartCode = "\nbool periods[ndims]; for (int i = 0; i < ndims; i++) periods[i] = false;\n" ++ 
                 "cartComm = MPI::COMM_WORLD.Create_cart(ndims, &dimSizes.front(), periods, true);\n\n"
  -- init nodeCoordRanks array code
  let dims = [0..((length dimNames)-1)]
  coordInitLoops <- initNodeRanks "coordRanks" "cartComm" dims $ zip dims dims
  let rankCode = "{\n int coord[ndims];\n" ++ coordInitLoops ++ "\n}\n"
  -- get root node rank
  let rootRankCode = "rootRank = coordRanks" ++ (concat $ replicate (length dimNames) "[0]") ++ ";\n"
  -- output to streams
  output "decls" decls
  output "init" $ 
    "\n// Init global cartesian topology\n" ++ 
    "if (ndims > 0) {\n" ++ 
    initCode ++ cartCode ++ rankCode ++ rootRankCode ++ 
    "\n} else {\n"++
    "  std::cerr << \"WARNING: ndims = 0!!!\";\n"++
    "  std::cout << \"WARNING: ndims = 0!!!\";\n"++
    "}\n"
  return ()

{--- |coordVarToNodeRank coordVar rankVar dimTy hereOrAxis. Takes a coordVar (tuple of integers), and 
-- |generates code to assign the rank of the node defined by coordVar and dimTy (the dimensions
-- |the coords refer to), to rankVar, where any dims not in coordVar and dimTy are sets to
-- |this node's coord values if hereOrAxis is True, or 0 if here or Axis is False.
coordVarToNodeRank :: Monad m => Maybe Id -> Val m -> Val m -> Ty -> Bool -> GenM1 m Code
coordVarToNodeRank mapVid coordVar@(VarV vty vid) rankVar dimTy hereOrAxis = do
  -- align coordVar and dimTy to get dim name for each coord
  let dimVarPairs = alignTrees "Back:CartTop:coordVarToNodeRank" dimTy vid
  let dimVarPairs' = map (\(VarTy d, Lf v) -> (d,v)) dimVarPairs
  -- use global map of dim names to dim ints, to get dim ints to vars
  dimNamesToInts <- gets ((fromMaybe $ error "Back:CartTop:coordVarToNodeRank dimNamesToInts not in globals map.").(DM.lookup "dimNamesToInts").genGlobals)
  let dimIdxVarPairs = map (\(dn, v) -> (fromIntVal $ fromMaybe (error "Back:CartTop:coordVarToNodeRank dim name not in global map.") $ DM.lookup (Lf $ IdOV dn) dimNamesToInts, v)) dimVarPairs'
  -- for all dim ints in program, either lookup from map, or use 0/thisCoord[i]
  let ndims = DM.size dimNamesToInts
  let dimExps = map (\dim -> fromMaybe (if hereOrAxis then "thisCoord["++(show dim)++"]" else "0") $ lookup dim dimIdxVarPairs) [1..ndims] 
  -- turn the exp for each coord into coordRanks[0][v2][v3]...
  let rankExp = (fromMaybe "coordRanks" mapVid) ++ (concat $ map (\cv -> "[" ++ cv ++ "]") dimExps)
  -- create assignment/return expression.
  return rankExp
coordVarToNodeRank p0 p1 p2 p3 p4 = error $ "Back:CartTop:coordVarToNodeRank parameter error: " ++ 
                                  (show p0) ++ (show p1) ++ (show p2) ++ (show p3) ++ (show p4)

-- |coordVarToNodeRank2 coordVar rankVar dimTy hereOrAxis. Takes a coordVar (tuple of integers), and 
-- |generates code to assign the rank of the node defined by coordVar and dimTy (the dimensions
-- |the coords refer to), to rankVar, where any dims not in coordVar and dimTy are sets to
-- |this node's coord values if hereOrAxis is True, or 0 if here or Axis is False.
coordVarToNodeRank2 :: Monad m => Maybe Id -> Val m -> Val m -> Ty -> Ty -> GenM1 m Code
coordVarToNodeRank2 mapVid coordVar@(VarV vty vid) rankVar dimTy mirDimTy = do
  -- align coordVar and dimTy to get dim name for each coord
  let dimVarPairs = alignTrees "Back:CartTop:coordVarToNodeRank2:" dimTy vid
  let dimVarPairs' = map (\(VarTy d, Lf v) -> (d,v)) dimVarPairs
  -- use global map of dim names to dim ints, to get dim ints to vars
  dimNamesToInts <- gets ((fromMaybe $ error "Back:CartTop:coordVarToNodeRank2 dimNamesToInts not in globals map.").(DM.lookup "dimNamesToInts").genGlobals)
  let dimIdxVarPairs = map (\(dn, v) -> (fromIntVal $ fromMaybe (error "Templates:varNodeToRank: dim name not in global map.") $ DM.lookup (Lf $ IdOV dn) dimNamesToInts, v)) dimVarPairs'
  -- get set of dim idxs that should be mirrored
  let mirDimNames = getVarsInTy mirDimTy
  let mirDimIndices = DS.map (\n -> fromIntVal $ fromMaybe (error "Back:CartTop:coordVarToNodeRank2  dim name not in global map.") $ DM.lookup (Lf $ IdOV n) dimNamesToInts) mirDimNames
  -- for all dim ints in program, either lookup from map, or use 0/thisCoord[i]
  let ndims = DM.size dimNamesToInts
  let dimExps = map (\dim -> fromMaybe (if DS.member dim mirDimIndices then "thisCoord["++(show dim)++"]" else "0") $ lookup dim dimIdxVarPairs) [0..(ndims-1)] 
  -- turn the exp for each coord into coordRanks[0][v2][v3]...
  let rankExp = (fromMaybe "coordRanks" mapVid) ++ (concat $ map (\cv -> "[" ++ cv ++ "]") dimExps)
  -- create assignment/return expression.
  return rankExp
coordVarToNodeRank2 p0 p1 p2 p3 p4 = error $ "Back:CartTop:coordVarToNodeRank2 parameter error: " ++ 
                               (show p0) ++ (show p1) ++ (show p2) ++ (show p3) ++ (show p4)-}

-- |coordVarToNodeRank2 coordVar rankVar cartDims dimTy mirDimTy. Takes a coordVar (tuple of integers), and 
-- |generates code to assign the rank of the node defined by coordVar and dimTy (the dimensions
-- |the coords refer to), to rankVar. Any dims not in coordVar and dimTy are set to
-- |this node's coord values if that dim is in mirDimTy, or 0 otherwise.
coordVarToNodeRank3 :: Monad m => Val m -> Val m -> Ty -> Ty -> Ty -> GenM1 m Code
coordVarToNodeRank3 coordVar@(VarV vty vid) rankVar cartDims dimTy mirDimTy = do
  let errPfx = \msg -> error $ "Back:CartTop:coordVarToNodeRank3:" ++ msg
  -- get the cartesian toplogy to use
  globs <- gets genGlobals
  let subCarts = fromMaybe (errPfx "sub carts not in genGlobals!") $ DM.lookup "subCarts" globs
  let cartDimNames = getVarsInTy cartDims
  let nldims = DS.size cartDimNames
  let cartDimNameList = Lf $ ListOV $ map (LitOV . StrVal) $ DS.toAscList cartDimNames
  let dimNamesToIdxs = fromMaybe (errPfx "dim names not in genGlobals!") $ DM.lookup "dimNamesToInts" globs
  let ndims = DM.size dimNamesToIdxs
  let cartDimIndices = DS.map (\n -> fromIntVal $ fromMaybe (errPfx "1:dim name not in global map.") $ DM.lookup (Lf $ IdOV n) dimNamesToIdxs) cartDimNames
  (_, mapVid) <- (case cartDimIndices == DS.fromList [0..(ndims-1)] of
                  -- if is the global topology
                  True -> return ("cartComm", "coordRanks")
                  -- if is a sub topology
                  False -> do
                    case DM.lookup cartDimNameList subCarts of
                      -- cart already generated
                      Just (ListV [IdV commVid, IdV mapVid]) -> return (commVid, mapVid)
                      -- cart not generated
                      Nothing -> errPfx $ "sub grid not created for " ++ (show cartDims) ++ "\n")
  -- align coordVar and dimTy to get dim name for each coord
  let dimVarPairs = alignTrees "Back:CartTop:coordVarToNodeRank3:" dimTy vid
  let dimVarPairs' = map (\(VarTy d, Lf v) -> (d,v)) dimVarPairs
  -- use global map of dim names to dim ints, to get dim ints to vars
  let dimIdxVarPairs = map (\(dn, v) -> (fromIntVal $ fromMaybe (errPfx "2:dim name not in global map.") $ DM.lookup (Lf $ IdOV dn) dimNamesToIdxs, v)) dimVarPairs'
  -- get set of dim idxs that should be mirrored
  let mirDimNames = getVarsInTy mirDimTy
  let mirDimIndices = DS.map (\n -> fromIntVal $ fromMaybe (errPfx "2:dim name not in global map.") $ DM.lookup (Lf $ IdOV n) dimNamesToIdxs) mirDimNames
  -- get map between local dims and global dims
  let locToGlobDims = zip [0..(nldims-1)] $ DS.toAscList cartDimIndices
  -- for all dim ints in program, either lookup from map, or use 0/thisCoord[i]
  let dimExps = map (\(ldim,gdim) -> fromMaybe (if DS.member gdim mirDimIndices then "thisCoord["++(show gdim)++"]" else "0") $ lookup gdim dimIdxVarPairs) locToGlobDims
  -- turn the exp for each coord into coordRanks[0][v2][v3]...
  let rankExp = mapVid ++ (concat $ map (\cv -> "[" ++ cv ++ "]") dimExps)
  -- create assignment/return expression.
  return rankExp
coordVarToNodeRank3 p0 p1 p2 p3 p4 = error $ "Back:CartTop:coordVarToNodeRank3 parameter error: " ++ 
                               (show p0) ++ (show p1) ++ (show p2) ++ (show p3) ++ (show p4)

-- |varToNodeRank inV rankV cartDims dimTy mirDimTy. Returns code that assigns
-- |to rankV the rank that the value in inV should live at. dimTy is the dim that
-- |we are partitioning across. 
varToNodeRank :: (Monad m, MonadCatch m) => Val m -> Val m -> Ty -> Ty -> Ty -> GenM1 m Code
varToNodeRank inV rankV@(VarV _ (Lf rankVid)) cartDims dimTy mirDimTy = do
  -- hash var
  hashVid <- newInt >>= (return.("hash"++).show)
  let hashV = VarV intTy (Lf hashVid)
  let decHashV = "int " ++ hashVid ++ " = 0;\n"
  (CodeV hashCode) <- hashVar [inV, hashV]
  -- TODO convert hash to node coord tuple of same arity as dimTy
  -- WARNING: Only currently supports 1D dim types
  -- (get idx of the dim)
  case dimTy of
    -- 1D dim
    (Lf (VarTy dimName)) -> do
      globs <- gets genGlobals
      let dimNames = fromMaybe (error $ "Back:CartTop:varToNodeRank:dim names not in genGlobals!") $ DM.lookup "dimNamesToInts" globs
      let dimIdx = fromMaybe (error $ "Back:CartTop:varToNodeRank:dim " ++ (show dimName) ++ " not in dimNamesToInts.\n") $ DM.lookup (Lf $ IdOV dimName) dimNames
      -- (get size of the dim)
      let dimSize = "dimSizes[" ++ (show dimIdx) ++ "]"
      -- (currently use hashVar for coord and mod hash by dim size)
      let coordCode = hashVid ++ " = (unsigned int)" ++ hashVid ++ " % " ++ dimSize ++ ";\n"
      -- (assert that coord is in correct range)
      let assCode = "mpiAssert(" ++ hashVid ++ " >= 0 && " ++ hashVid ++ " < " ++ dimSize ++ 
                    ", \"varToNodeRank: coord " ++ hashVid ++ " out of range.\");\n" 
      -- convert node coords to rank
      rankCode <- coordVarToNodeRank3 hashV rankV cartDims dimTy mirDimTy
      -- (assert that rank is in correct range)
      let assCode2 = "mpiAssert(" ++ rankVid ++ " >= 0 && " ++ rankVid ++ " < " ++ "cartComm/* WARNING CHANGE TO USE SUB CARTS TOO */" ++  
                     ".Get_size(), \"varToNodeRank: rank " ++ rankVid ++ " out of range.\");\n"
      -- return
      return $ decHashV ++ hashCode ++ coordCode ++ assCode ++ rankVid ++ " = " ++ rankCode ++ ";\n" ++ assCode2
    -- Null dim (only at root)
    (Lf (LfTy "Null" [])) -> do
      return $ rankVid ++ " = 0; // rank always 0 for null top dimension\n" 
    -- other
    other -> error $ "CartTop:varToNodeRank: only currently supports 1D dims: " ++ (show dimTy)

-- |varToSubNodeRankV codeVid inVid outVid parDimTy mirrDimTy. Returns
-- |node rank for a given value, but takes names of local template vars
-- |rather than VarVs.
varToNodeRankV :: (Monad m, MonadCatch m) => Id -> IdTree -> Id -> Ty -> Ty -> Ty -> GenM m
varToNodeRankV codeVid inVid outVid cartDims dimTy mirDimTy = do
  -- get vars
  inV <- getLocalVar inVid
  outV <- getLocalVal outVid
  -- call varToNodeRank
  code <- varToNodeRank inV outV cartDims dimTy mirDimTy
  -- bind code to codeVid
  setLocalVal codeVid $ CodeV code
  -- return
  return ()  

-- |hasDataPred parDims mirrDims. Generates a predicate
-- |that will return true if there is data on the current
-- |node for the dims given.
hasDataPred :: Monad m => Ty -> Ty -> GenM1 m Code
hasDataPred parDims mirrDims = do
  -- get dim names to idxs
  globs <- gets genGlobals
  let dimNames = fromMaybe (error $ "Back:CartTop:hasDataPred:dim names not in genGlobals!") $ DM.lookup "dimNamesToInts" globs
  -- get dim idxs in par dims, and in mirr dims
  let errMsg = error "Back:CartTop:hasDataPred: dim name not in global map."
  let parDimNames = getVarsInTy parDims
  let mirDimNames = getVarsInTy mirrDims 
  let parDimIndices = DS.map (\n -> fromIntVal $ fromMaybe errMsg $ DM.lookup (Lf $ IdOV n) dimNames) parDimNames
  let mirDimIndices = DS.map (\n -> fromIntVal $ fromMaybe errMsg $ DM.lookup (Lf $ IdOV n) dimNames) mirDimNames
  -- get dims not mentioned in mirr or part
  let remDimIndices = (DS.fromList [0..((DM.size dimNames) - 1)]) `DS.difference` parDimIndices `DS.difference` mirDimIndices
  -- make predicate
  case DS.toAscList remDimIndices of
    [] -> return "true"
    l  -> return $ DL.intercalate " && " $ map (\d -> "thisCoord[" ++ (show d) ++ "] == 0") l

-- |genHasDataPred predExpVname. Generates predicate that returns true
-- |if the dist given implies there will be data on the current node,
-- |and binds the predicate as code to predExpVname.
genHasDataPred :: Monad m => Id -> Ty -> Ty -> GenM m
genHasDataPred predExpVname parDims mirrDims = do
  -- gen pred
  pred <- hasDataPred parDims mirrDims
  -- bind to var name
  setLocalVal predExpVname $ CodeV pred
  return ()

-- |genSubCartV commV coordMapV dims. Generates code to create
-- |a new sub cartesian toplology, where only the dims in dims remain.
-- |The code to create it is bound to codeV, the new comm var bounds to 
-- |commVname, and the new coord map to coordMapV. If all dims are included
-- |the this returns the global cart topology, and doesn't create another one.
-- |Code is added to init stream. If already created for these dims, doesn't recreate.
genSubCartV :: (Monad m, MonadCatch m) => Id -> Id -> Ty -> GenM m
genSubCartV commVname coordMapVname dims = do
  -- get dim names to idxs
  globs <- gets genGlobals
  let dimNames = getVarsInTy dims
  let dimNamesToIdxs = fromMaybe (error $ "Back:CartTop:getSubCart:dim names not in genGlobals!") $ DM.lookup "dimNamesToInts" globs
  let ndims = DM.size dimNamesToIdxs
  -- get indices of dims to include
  let errMsg = error "Back:CartTop:genSubCart: dim name not in global map."
  let dimIndices = DS.map (\n -> fromIntVal $ fromMaybe errMsg $ DM.lookup (Lf $ IdOV n) dimNamesToIdxs) dimNames
  -- see if use global or not
  case dimIndices == DS.fromList [0..(ndims-1)] of
    -- use global cart
    True -> case ndims of
        -- no dims
        0 -> do
          varExp commVname "" "MPI::COMM_WORLD" intTy
          varExp coordMapVname "" "ERROR SHOULD NOT NEED coordRanks WITH ndims = 0!" intTy
        -- one or more dims
        _ -> do
          varExp commVname "" "cartComm" intTy
          varExp coordMapVname "" "coordRanks" intTy
          return () 
    -- use a sub cart
    False -> do
      -- check if this sub cart has already been defined
      let subCarts = fromMaybe (error $ "Back:CartTop:getSubCart:sub carts not in genGlobals!") $ DM.lookup "subCarts" globs
      let dimNameList = Lf $ ListOV $ map (LitOV . StrVal) $ DS.toAscList dimNames
      case DM.lookup dimNameList subCarts of
        -- cart already generated
        Just (ListV [IdV commVid, IdV mapVid]) -> do
          varExp commVname "" commVid intTy
          varExp coordMapVname "" mapVid intTy
          return () 
        -- need to generate this subcart
        Nothing -> do
          genTrace "entering CartTopology:genSubCartV/create new sub cart"
          -- get name to distinguish new var names
          vid <- newInt >>= (return.("CartVar"++).show)
          -- generate code for remain_dims in MPI_Cart_sub
          let remDimsList = map (\d -> if DS.member d dimIndices then True else False) [0..(ndims-1)]
          newVar(Lf $ "remDims"++vid) (Lf $ ListTy boolTy)
          runGen "litArr" ("decRemDims"++vid) [IdV ("remDims"++vid), ListV $ map (LitV . BolVal) remDimsList]
          (VarV _ (Lf remVid)) <- getLocalVar (Lf ("remDims"++vid))
          -- call create sub cart
          newVar (Lf commVname) intTy
          (VarV _ (Lf commVid)) <- getLocalVar (Lf commVname)
          let declComm = "static MPI::Cartcomm " ++ commVid ++ ";\n"
          let createSubCart = commVid ++ " = cartComm.Sub(" ++ remVid ++ ");\n"
          -- create new coord map
          let nldims = DS.size dimIndices
          let globDimIdxList = DS.toAscList dimIndices
          let locDimIdxList = [0..(nldims-1)]
          let mapVid = "coordRanks" ++ vid
          let mapDecl = "int " ++ mapVid ++ (concat $ map (\d -> "[maxNodesPerDim]") locDimIdxList) ++ ";\n"
          varExp coordMapVname "" mapVid intTy
          initMap <- initNodeRanks mapVid commVid locDimIdxList $ zip globDimIdxList locDimIdxList
          -- put together setup code, and add to init stream
          let code = "<decRemDims" ++ vid ++ ">" ++ createSubCart ++ "{\n" ++ "int coord[" ++ (show nldims) ++ "];\n" ++ initMap ++ "\n}\n"
          output "decls" $ "// Sub grid communicator for dims " ++ (show dims) ++ "\n" ++ declComm ++ mapDecl ++ "\n\n"
          output "init" $ "// Init sub grid communicator for dims " ++ (show dims) ++ "\n" ++ code
          -- add vars to globals
          let vars = ListV [IdV commVid, IdV mapVid]
          modify (\st -> st { genGlobals=DM.adjust (DM.insert dimNameList vars) "subCarts" (genGlobals st)} )
          genTrace "leaving CartTopology:genSubCartV/create new sub cart"
          return ()  

-- |getDimSize varName dimTy. Binds an expression giving the number of
-- |nodes in the dimensions in dimTy, to a var called varName.
getDimSize :: Monad m => Id -> Ty -> GenM m
getDimSize vname dimTy = do
  -- get dim ids
  let dims = getVarsInTy dimTy
  -- get dim names to idxs
  globs <- gets genGlobals
  let errMsg = error "Back:CartTop:getDimSize: dim name not in global map."
  let dimNames = fromMaybe (error $ "Back:CartTop:getDimSize:dim names not in genGlobals!") $ DM.lookup "dimNamesToInts" globs
  let dimIndices = DS.map (\n -> fromIntVal $ fromMaybe errMsg $ DM.lookup (Lf $ IdOV n) dimNames) dims
  -- get dim sizes of individual dims
  let dimSizes = map (\i -> "dimSizes[" ++ (show i) ++ "]") $ DS.toList dimIndices
  -- multiply together
  let total = foldl (\a -> \b -> a ++ "*" ++ b) "1" dimSizes
  -- bind to var 
  --setLocalVal vname $ CodeV total
  varExp vname "" total intTy
  return ()


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
module Compiler.Back.TypeNames where

import Compiler.Types2.TypeInfo (typeModeNames)
import Compiler.Back.Graph
import Compiler.Back.GenDecls

import Data.Maybe (fromMaybe)
import Data.List (stripPrefix)

nameTy :: String -> LfTy
nameTy n = (LfTy n [])

namedTy :: String -> [Ty] -> LfTy
namedTy n l = (LfTy n l)

eqTys :: LfTy -> LfTy
eqTys tin@(LfTy name l) = case (name, map (mapTree eqTys) l) of
  -- vectors
  ("LVec", [et]) -> namedTy "Vec" [et]
  -- maps
  ("VecMap", [Tup [kt, vt],_,_,_]) -> namedTy "Map" [kt, vt]
  ("LMap", [_,kt,vt,_]) -> namedTy "Map" [kt,vt]
  ("DMap", [_,kt,vt,_,_,_,_]) -> namedTy "Map" [kt, vt]
  -- Get rid of pointers
  ("Ptr", [(Lf t)]) -> t  
  ("SPtr", [(Lf t)]) -> t
  -- everything else the same
  other -> tin   

-- |Returns true for all types that should be copied by 
-- |value rather than by pointer.
copyByVal :: Ty -> Bool
copyByVal ty = case ty of
  (Lf (LfTy "SPtr" [Lf (LfTy "VecMap" _)])) -> True
  (Lf (LfTy "DMap" l)) -> True 
  _ -> False

-- |Returns the value to use when creating a fresh instance of this
-- |type. 
defaultInitializer :: Monad m => Ty -> Id -> GenM1 m Id
defaultInitializer (Lf lfTy) tyId = case lfTy of
  (LfTy "SPtr" [Lf (LfTy "VecMap" _)]) -> return $ "new " ++ (init $ fromMaybe tyId $ stripPrefix "boost::shared_ptr<" tyId)
  (LfTy "DMap" l) -> return $ "new " ++ (init $ fromMaybe tyId $ stripPrefix "boost::shared_ptr<" tyId)
  other -> return ""
defaultInitializer other tyId = return ""

-- |getTypeName ty. Returns the C++ type
-- |to use for ty, or Nothing if this type should not
-- |be stored as a data structure.
getTypeName :: Monad m => LfTy -> [Maybe Id] -> GenM1 m (Maybe Id)
getTypeName lfTy children = case (lfTy, children) of
    -- mirrored type are themselves
    --(LfTy "Mirr" [ty], [tid]) -> return $ Just $ fromMaybe (error msg) tid
    -- distributed vector
    (LfTy "LVec" [et], [tid]) -> return $ Just $ "flocc::vec<" ++ (fromMaybe (error msg) tid) ++ " >"
    -- distributed maps
    {-(LfTy "DistMap" [kt, vt, kf, pf, nl], [ktid, vtid, _, _, _]) -> return $ Just $ "std::map<" ++ (fromMaybe (error msg) ktid) ++ ", " ++ (fromMaybe (error msg) vtid) ++ " >"
    (LfTy "DistHashMap" [kt, v2, kf, pf, nl], [ktid, vtid, _, _, _]) ->
      return $ Just $ "dense_hash_map<" ++ (fromMaybe (error msg) ktid) ++ ", " ++
                                           (fromMaybe (error msg) vtid) ++ ", " ++
                                           "hash<" ++ (fromMaybe (error msg) ktid) ++ " >, " ++ 
                                           "eq" ++ (fromMaybe (error msg) ktid) ++  " >"-}
    (LfTy "VecMap" [kvt, pkt, Lf (LfTy "Null" []), projt], [kvtid, pktid, sktid, projtid]) -> -- vec map with null secondary key
      return $ Just $ "flocc::vecmap<" ++ (fromMaybe (error $ msg ++ "/elT/"++ (show kvt)) kvtid) ++ ", " ++
                                          (fromMaybe (error $ msg ++ "/priKeyT/"++ (show pkt)) pktid) ++ ", " ++
                                          "char, " ++
                                          (fromMaybe (error $ msg ++ "/projFun/"++ (show projt)) projtid) ++ " >"
    (LfTy "VecMap" [kvt, pkt, skt, projt], [kvtid, pktid, sktid, projtid]) -> -- any other vecmap
      return $ Just $ "flocc::vecmap<" ++ (fromMaybe (error $ msg ++ "/elT/"++ (show kvt)) kvtid) ++ ", " ++
                                          (fromMaybe (error $ msg ++ "/priKeyT/"++ (show pkt)) pktid) ++ ", " ++
                                          (fromMaybe (error $ msg ++ "/secKeyT/"++ (show skt)) sktid) ++ ", " ++
                                          (fromMaybe (error $ msg ++ "/projFun/"++ (show projt)) projtid) ++ " >"
    (LfTy "LMap" [(Lf (LfTy mode [])), kt, v2, sf], [_, ktid, vtid, _]) -> case mode of
      -- hash map
      "Hsh" -> return $ Just $ "google::dense_hash_map<" ++ (fromMaybe (error msg) ktid) ++ ", " ++
                               (fromMaybe "char" vtid) ++ ", " ++
                               "flocc::hasher<" ++ (fromMaybe (error msg) ktid) ++ " >, " ++ 
                               "flocc::eq<" ++ (fromMaybe (error msg) ktid) ++  " > >"
    (LfTy "MultiMap" [mmKt, kvt], [mmKtid, kvtid]) -> -- a std::multimap
      return $ Just $ "std::multimap<" ++ (fromMaybe (error msg) mmKtid) ++ ", " ++
                                          (fromMaybe (error msg) kvtid) ++ " >" 
    -- redistributer
    (LfTy "Reparter" [elT, outT], [elTid, outTid]) -> 
      return $ Just $ "flocc::reparter<" ++ (fromMaybe (error msg) elTid) ++ ", " ++ (fromMaybe (error msg) outTid) ++ " >"                    
    -- iterators
    (LfTy "Iter" [colTy], [colTId]) -> return $ Just $ (fromMaybe (error msg) colTId) ++ "::iterator" 
    (LfTy "ConstIter" [colTy], [colTId]) -> return $ Just $ (fromMaybe (error msg) colTId) ++ "::iterator" --"::const_iterator" 
    (LfTy "IdxIter" [colTy], [colTId]) -> return $ Just $ (fromMaybe (error msg) colTId) ++ "::idx_iterator"
    -- pointers
    (LfTy "Ptr" [vTy], [vTId]) -> return $ Just $ (fromMaybe (error msg) vTId) ++ "*"
    (LfTy "SPtr" [vTy], [vTId]) -> return $ Just $ "boost::shared_ptr<" ++ (fromMaybe (error msg) vTId) ++ " >"
    -- distributed array
    {-(LfTy "DistArr" [idxTy, valty, layoutF, invLayoutF, partF, dims, mirrDims], [idxTid, valTid, _, _, _, _, _]) -> do
       -- get number of int's in flattened idxTy
       let flatIdxTy = flattenTree idxTy
       -- return template class
       return $ Just $ "SubArray<" ++ (fromMaybe (error msg) valTid) ++ ", " ++ (show $ length flatIdxTy) ++ ">"
    -- distributed array
    (LfTy "DistArrRoot" [idxTy, valty, layoutF, invLayoutF, partF, dims, mirrDims], [idxTid, valTid, _, _, _, _, _]) -> do
       -- get number of int's in flattened idxTy
       let flatIdxTy = flattenTree idxTy
       -- return template class
       return $ Just $ "RootArray<" ++ (fromMaybe (error msg) valTid) ++ ", " ++ (show $ length flatIdxTy) ++ ">"
    (LfTy "DistArr1D" [valTy, kf, vf, nl], [tid, _, _, _]) -> return $ Just $ "std::vector<" ++ (fromMaybe (error msg) tid) ++ " >"-}
    -- mpi datatype 
    (LfTy "MPIType" [], _) -> return $ Just "MPI::Datatype"
    -- used for distribution meta-data, not actual data types
    {-(LfTy "NullFun" [], _) -> return Nothing
    (LfTy "NullDim" [], _) -> return Nothing
    (LfTy "MirrDims" [], _) -> return Nothing
    (LfTy "DimDists" _, _) -> return Nothing
    (LfTy "Fringe" [], _) -> return Nothing
    (LfTy "Mirr" [], _) -> return Nothing
    (LfTy ('P':'a':'r':'t':_) [], _) -> return Nothing
    -- from DistHistDemo
    (LfTy "AllNodes" [], _) -> return Nothing
    (LfTy "snd" [], _) -> return Nothing
    (LfTy "fst" [], _) -> return Nothing
    (LfTy "modN" l, _) -> return Nothing
    (LfTy "Snd" [], _) -> return Nothing
    (LfTy "Fst" [], _) -> return Nothing
    (LfTy "ModN" l, _) -> return Nothing-}
    -- functions (TODO create fun_class?)
    (FunTy graph, _) -> return Nothing
    -- type modes
    (LfTy name [], _) -> case elem name typeModeNames of
      True  -> return Nothing
      False -> error $ "TypeNames:getTypeName: can't return type name for " ++ (show lfTy)
    _ -> error $ "TypeNames:getTypeName: can't return type name for " ++ (show lfTy)
  where msg = "getTypeName:couldn't generate type name for " ++ (show lfTy)

-- TODO ADD CONSTRUCTORS TO SUBARRAY, SO WE CAN ALWAYS CREATE SUBARRAYS, AND THEY CAN 
-- CREATE NEW UNDERLYING ROOT ARRAYS, IF NONE IS GIVEN      

getMPITypeName :: Monad m => Ty -> Maybe Id -> GenM1 m (Maybe (Id, Code))
getMPITypeName ty idv = case ty of
  -- scalars
  Lf lty -> case lty of
    -- scalar types
    _ | ty == intTy   -> return $ Just ("MPI::INT", "")
    _ | ty == uintTy  -> return $ Just ("MPI::UNSIGNED", "")
    _ | ty == floatTy -> return $ Just ("MPI::DOUBLE", "")
    _ | ty == boolTy  -> return $ Just ("MPI::C_BOOL", "")
    _ | ty == nullTy  -> return $ Nothing
  -- structs (not needed as packed)
    -- TODO just use packed and size of struct
  -- arrays
    -- TODO generate data type for this collection
  -- other collections
   -- TODO just use n copies of struct mpi data type
  other -> error $ "cant generate mpi type for " ++ (show ty)



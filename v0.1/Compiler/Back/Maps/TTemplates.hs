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
module Compiler.Back.Maps.TTemplates where

import Data.Maybe (fromMaybe)
import Control.Monad.State.Strict (gets)
import Control.Monad.Catch

import Compiler.Front.Common (ShowP(..))
import Compiler.Back.Graph
import Compiler.Back.GenDecls
import Compiler.Back.Gen
import Compiler.Back.Generators
import Compiler.Back.Templates
import Compiler.Back.Helper
import Compiler.Back.CartTopology

-- sorted vector templates

tmapTemplates :: (Monad m, MonadCatch m) => [(Id, Template m)]
tmapTemplates = [
    ("readTMap", t01),
    ("saveTMap1", t02 1),
    ("saveTMap2", t02 2), 
    ("maxTMap", t05),
    ("minTMap", t06),{-
    ("crossVMaps11", t07),
    ("unionVMaps1", t09),
    --("unionVMaps2", t10),
    ("unionVMaps3", t13),-}
    ("countTMap", t11),
    ("countTMapMirr", t12)
  ]

-- |readTMap template
t01 :: (Monad m, MonadCatch m) => Template m
t01 (Lf (LfTy "DMap" [mode1, kt1, vt1, ordF1, parF1, parD1, mirD1]) :-> 
     Lf (LfTy "DMap" [mode2, kt2, vt2, ordF2, parF2, parD2, mirD2]))
   (LFun _ inN outN)
   | mode1 == nameTy "Tree" && mode2 == nameTy "Stm" &&
     kt1 == kt2 && vt1 == vt2 = do
     -- check in and out dists are same
     assertM (return $ parD1 == parD2) "par dims don't match"
     assertM (return $ mirD1 == mirD2) "mirror dims don't match"
     -- get input var name 
     getVar (Lf "inMap") inN outVarName
     -- declare loop iterator and end iterator
     (TyV treeMapTy) <- getVal inN "treeMapTy"
     let iterTy = Lf $ LfTy "ConstIter" [treeMapTy] -- TODO !!! pass as shared_ptr, or just as is??? !!!
     newVar (Lf "it") iterTy
     newVar (Lf "end") iterTy 
     varExp "itBegin" "inMap" "<v>->begin()" iterTy
     varExp "itEnd" "inMap" "<v>->end()" iterTy
     runGenV "declareVarInit" "decIt" [Lf "it", Lf "itBegin"]
     runGenV "declareVarInit" "decEnd" [Lf "end", Lf "itEnd"]
     -- declare stream var
     varExp "itKey" "it" "<v>.second->v0" kt1
     varExp "itVal" "it" "<v>.second->v1" vt1
     setVar outN "streamVar" $ Tup [Lf "itKey", Lf "itVal"]
     -- if we know the maps size, pass it on (Note: this is the size of the global partitioned map)
     ifVarExists "count" inN "count" (setVar outN "count" $ Lf "count") (return ())
     -- when gen is called, generate loop
     setFun outN "gen" nt (\_ -> do
       -- gen consumers
       callAll outN "genConsumers" nt
       ifVarsExist [("init", outN, "initStream"), ("fin", outN, "finStream"), ("consume", outN, "consumers")] (do
         -- local data pred
         genHasDataPred "hasData" parD1 mirD1
         -- output code
         outMain $
           "<init>\n"++
           "if (<hasData>) {\n"++
           "<decIt><decEnd>\n"++
           "for (; <it> != <end>; <it>++) {\n"++
           "  <consume>\n"++
           "}\n"++
           "}\n"++
           "<fin>\n"
         ) (return ())
       return ())
t01 t n = terr' t n

-- |saveTMap1 template
-- |version == 1 => input stream is already ordered by multimap keys
-- |version == 2 => input stream is not ordered by multimap keys
t02 :: (Monad m, MonadCatch m) => Int -> Template m
t02 version 
   ((Lf (LfTy "DMap" [mode1, keyT1, valT1, ordF1, parF1, parD1, mirD1])) :-> 
     (Lf (LfTy "DMap" [mode2, keyT2, valT2, ordF2, parF2, parD2, mirD2])))
   (LFun _ inN outN)
   | (version == 1 || version == 2) &&
     keyT1 == keyT2 && valT1 == valT2 && 
     mode1 == nameTy "Stm" && mode2 == nameTy "Tree" = do
     -- check in and out dims are the same
     assertM (return $ parD1 == parD2) $ "par dims don't match"
     assertM (return $ mirD1 == mirD2) $ "mirror dims don't match"
     -- get input stream vars
     getVar (Lf "svar") inN "streamVar"
     -- declare output element struct
     -- TODO only copy if svar is not a struct...
     newStructVar (Lf "el") $ Tup [keyT1, valT1]
     runGenV "declareVar" "decEl" [Lf "el"]
     runGenV "assignVar" "appCopy" [Lf "el", Lf "svar"] 
     -- declare output multimap var    
     let (Lf (FunTy ordFun)) = ordF1
     (ordDomTy :-> ordRanTy) <- getGraphTy ordFun
     let outTy = Lf $ LfTy "MultiMap" [ordRanTy, Tup [keyT1, valT1]]
     setVal outN "treeMapTy" (TyV outTy)
     tn <- getTemplateName
     outmapTyName <- genTypeName outTy >>= (return . (fromMaybe (error $ "Templates:" ++ tn ++ " can't get type name of " ++ (show outTy))))
     varExp "newTreeMap" "" ("new " ++ outmapTyName) (Lf $ LfTy "Ptr" [outTy])
     ifnVarInit "decOut" outVarName (Lf "outMap") (Lf $ LfTy "SPtr" [outTy]) (Just $ Tup [Lf "newTreeMap"])
     -- create multimap key var, and projection function app     
     newStructVar (Lf "mmKey") ordRanTy
     runGenV "declareVar" "decMMKey" [Lf "mmKey"]
     genTyFunV "appKeyProj" ordF1 (Lf "svar") n0 (Lf "mmKey")
     -- get types of multimap key, and key-value pair
     runGenV "genTyName" "mmKeyTy" [Lf "mmKey"]
     runGenV "genTyName" "elTy" [Lf "el"]
     -- pass along multimap type to consumers
     setVal outN "treeMapTy" (TyV outTy)
     -- if we know the maps size, pass it on
     ifVarExists "count" inN "count" (setVar outN "count" $ Lf "count") (return ())
     -- when gen is called, generate loop
     setFun outN "genConsumers" nt (\_ -> do
       -- add blocks to stream producer
       outputDecl outN "// begin <tem> decl\n<decOut>// end <tem> decl\n"
       addCode inN "initStream" "<decEl><decMMKey>" 
       addCode inN "consumers" $ 
         "// BEGIN <tem> consume:\n"++
         "<appCopy>\n<appKeyProj>\n"++ -- pack key-value in struct, and project out key to index by
         "<outMap>->insert(" ++ -- insert into map
           (if version == 1 then "<outMap>->end(), " else "") ++ -- if input stream is sorted by multimap keys then give location hint
           "std::pair<<mmKeyTy>, <elTy> >(<mmKey>, <el>));\n"++ -- packed value
         "// END <tem> consume\n"
       addCode inN "finStream" ""
       return ())
t02 version t n = terr' t n


-- TODO
-- could add optimized mirror that uses a non-standard allocator
-- to directly copy one std::multimap to other processes.

-- gatherVMap :: DMap Vec k v of pf d m -> DMap Vec k v FNull FNull () ()
-- allgatherVMap :: DMap Vec k v of pf d m -> DMap Vec k v FNull FNull () (d,m)
  -- it would be good to be able to say above pf => restriction of pf
  -- and instead of d => (), d => d - d1
  -- e.g. DMap Vec k v of pf d m -> DMap Vec k v FNull (pf - pf1(d1)) (d - d1) (m + d1)

-- bcastVMap :: DMap Vec k v of pf () () -> DMap Vec k v of FNull () m
-- scattVMap :: DMap Vec k v of pf () () -> DMap Vec k v of pf2 d () -- does of mean order of local parts, or order of whole?
-- mirrVMap :: DMap Vec k v of pf d m1 -> DMap Vec k v of pf d (m1,m2)

-- |countTMap template
t11 :: (Monad m, MonadCatch m) => Template m
t11 (Lf (LfTy "DMap" [mode, kt, vt, sf, pf, pd, md]) :-> numTy)
   (LFun _ inN outN)
   | mode == nameTy "Tree" && numTy == intTy = do
     -- get input var name 
     getVar (Lf "inMap") inN outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "cv") intTy
     newVar (Lf "tmp") intTy
     -- when gen is called, generate loop
     setFun outN "gen" nt (\_ -> do
       -- local data pred
       genHasDataPred "hasData" pd md
       -- if we know the list's length
       ifVarExists "count" inN "count" (
         -- then use listCount from producers
         outMain $ "// <tem>\n<decOut><cv> = <count>;\n") (
         -- else add code to count lists
         outMain $
           "// <tem>\n<decOut>\nint <tmp> = 0;"++
           "if (<hasData>) <tmp> = <inMap>->size();\n"++
           "MPI::COMM_WORLD.Allreduce(&<tmp>, &<cv>, 1, MPI::INT, MPI::SUM);\n")
       return ())
t11 t n = terr' t n

-- |countTMapMirr template
t12 :: (Monad m, MonadCatch m) => Template m
t12 (Lf (LfTy "DMap" [mode, kt, vt, sf, pf, pd, md]) :-> numTy)
   (LFun _ inN outN)
   | mode == nameTy "Tree" && numTy == intTy = do
     -- get input var name 
     getVar (Lf "inMap") inN outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "cv") intTy
     -- when gen is called, generate loop
     setFun outN "gen" nt (\_ -> do
       -- local data pred
       genHasDataPred "hasData" pd md
       -- if we know the list's length
       ifVarExists "count" inN "count" (
         -- then use listCount from producers
         outMain $ "// <tem>\n<decOut><cv> = <count>;\n") (
         -- else add code to count lists
         outMain $ "// <tem>\n<decOut>\n<cv> = <inMap>->size();\n")
       return ())
t12 t n = terr' t n

-- |maxTMap template
t05 :: (Monad m, MonadCatch m) => Template m
t05 (Tup [Tup [kt1, vt1] :-> wt1, Tup [wt2, wt3] :-> wt4, wt5,
     Lf (LfTy "DMap" [mode1, kt2, vt2, ordF1, parF1, parD1, mirD1])] :-> wt6)
   (LFun _ (LTup _ [projN, combineN, w0N, inN]) outN)
   | mode1 == nameTy "Tree" && match wt1 [wt2,wt3,wt4,wt5,wt6] &&
     kt1 == kt2 && vt1 == vt2 = do
     -- get input var name 
     getVar (Lf "inMap") inN outVarName
     getVar (Lf "val0") w0N outVarName
     -- create output var
     ifnVar "decOut" outVarName (Lf "outVal") wt3
     -- create temp vars
     newStructVar (Lf "val1") wt1
     runGenV "declareVarInit" "decVal1" [Lf "val1", Lf "val0"]
     newStructVar (Lf "val2") wt1
     runGenV "declareVarInit" "decVal2" [Lf "val2", Lf "val0"]
     (TyV treeMapTy) <- getVal inN "treeMapTy"
     newVar (Lf "iter") $ namedTy "ConstIter" [treeMapTy]
     runGenV "declareVar" "decIter" [Lf "iter"]
     runGenV "assignVar" "copyToOut" [Lf "outVal", Lf "val2"] 
     -- create projection function app
     varExp "el" "iter" "(*<v>).second" $ Tup [kt1, vt1]
     genFunV "appProjFun" projN (Lf "el") w0N (Lf "val1")
     -- declare AllReduce Op
     combineFun <- getFun combineN
     genTrace "maxTMap:got combineFun"
     runGen "reduceFun" "redFunName" [TyV wt1, combineFun]
     genTrace "maxTMap:generated reduceFun"
     newVar (Lf "redOp") intTy
     output "decls" "MPI::Op <redOp>;\n\n"
     output "init" "<redOp>.Init(&<redFunName>, true);\n\n"
     -- generate code
     setFun outN "gen" nt (\_ -> do
       -- prep for allreduce
       runGenV "genTyName" "resTyName" [Lf "val1"]
       -- local data for this dist
       genHasDataPred "hasData" parD1 mirD1
       genSubCartV "localComm" "localRanks" parD1
       -- output code
       outputDecl outN "// begin <tem> decl\n<decOut>// end <tem> decl"
       outMain $
         "// begin <tem>\n"++
         "<decVal2>\n"++
         "if (<hasData>) {\n"++
         -- get local max
         "  <decVal1>\n<decIter>\n"++
         "  <iter> = <inMap>->end();\n"++ -- try and get last element
         "  <iter>--;\n"++
         "  if (<iter> != <inMap>->end()) { <appProjFun> }\n"++
         -- allreduce it to find global max
         "  <localComm>.Allreduce(&<val1>, &<val2>, sizeof(<resTyName>), MPI::BYTE, <redOp>);\n"++
         "}\n"++
         -- if local comm isn't the global one, broadcast to any remaining ones 
         "if (<localComm> != cartComm) {\n"++
         "  cartComm.Bcast(&<val2>, sizeof(<resTyName>), MPI::BYTE, rootRank);\n" ++
         "}\n"++
         "<copyToOut>\n"++
         "// end <tem>\n"
       return ())
t05 t n = terr' t n

-- |minVMap template
t06 :: (Monad m, MonadCatch m) => Template m
t06 (Tup [Tup [kt1, vt1] :-> wt1, Tup [wt2, wt3] :-> wt4, wt5,
     Lf (LfTy "DMap" [mode1, kt2, vt2, ordF1, parF1, parD1, mirD1])] :-> wt6)
   (LFun _ (LTup _ [projN, combineN, w0N, inN]) outN)
   | mode1 == nameTy "Tree" && match wt1 [wt2,wt3,wt4,wt5,wt6] &&
     kt1 == kt2 && vt1 == vt2 = do
     -- get input var name 
     getVar (Lf "inMap") inN outVarName
     getVar (Lf "val0") w0N outVarName
     -- create output var
     ifnVar "decOut" outVarName (Lf "outVal") wt3
     -- create temp vars
     newStructVar (Lf "val1") wt1
     runGenV "declareVarInit" "decVal1" [Lf "val1", Lf "val0"]
     newStructVar (Lf "val2") wt1
     runGenV "declareVarInit" "decVal2" [Lf "val2", Lf "val0"]
     (TyV treeMapTy) <- getVal inN "treeMapTy"
     newVar (Lf "iter") $ namedTy "ConstIter" [treeMapTy]
     runGenV "declareVar" "decIter" [Lf "iter"]
     runGenV "assignVar" "copyToOut" [Lf "outVal", Lf "val2"] 
     -- create projection function app
     varExp "el" "iter" "(*<v>).second" $ Tup [kt1, vt1]
     genFunV "appProjFun" projN (Lf "el") w0N (Lf "val1")
     -- declare AllReduce Op
     combineFun <- getFun combineN
     genTrace "maxVMap:got combineFun"
     runGen "reduceFun" "redFunName" [TyV wt1, combineFun]
     genTrace "maxVMap:generated reduceFun"
     newVar (Lf "redOp") intTy
     output "decls" "MPI::Op <redOp>;\n\n"
     output "init" "<redOp>.Init(&<redFunName>, true);\n\n"
     -- generate code
     setFun outN "gen" nt (\_ -> do
       -- prep for allreduce
       runGenV "genTyName" "resTyName" [Lf "val1"]
       -- local data for this dist
       genHasDataPred "hasData" parD1 mirD1
       genSubCartV "localComm" "localRanks" parD1
       -- output code
       outputDecl outN "// begin <tem> decl\n<decOut>// end <tem> decl\n"
       outMain $
         "// begin <tem>\n"++
         "<decVal2>\n"++
         "if (<hasData>) {\n"++
         -- get local max
         "  <decVal1>\n<decIter>\n"++
         "  <iter> = <inMap>->begin();\n"++
         "  if (<iter> != <inMap>->end()) { <appProjFun> }\n"++
         -- allreduce it to find global max
         "  <localComm>.Allreduce(&<val1>, &<val2>, sizeof(<resTyName>), MPI::BYTE, <redOp>);\n"++
         "}\n"++
         -- if local comm isn't the global one, broadcast to any remaining ones 
         "if (<localComm> != cartComm) {\n"++
         "  cartComm.Bcast(&<val2>, sizeof(<resTyName>), MPI::BYTE, rootRank);\n" ++
         "}\n"++
         "<copyToOut>\n"++
         "// end <tem>\n"
       return ())
t06 t n = terr' t n

-- |crossVMaps11 template
{-t07 :: (Monad m, MonadCatch m) => Template m
t07 (Tup [Lf (LfTy "DMap" [mode1, kt1, vt1, ordF1, parF1, parD1, mirD1]),
          Lf (LfTy "DMap" [mode2, ity1, wt1, ordF2, parF2, parD2, mirD2])] :-> 
     Lf (LfTy "DMap" [mode3, Tup [kt2, ity2], Tup [vt2, wt2], ordF3, parF3, parD3, mirD3]))
   (LFun _ (LTup _ [inN1, inN2]) outN)
   | mode1 == nameTy "Stm" && mode2 == nameTy "Vec" && mode3 == nameTy "Stm" &&
     kt1 == kt2 && vt1 == vt2 && ity1 == ity2 && wt1 == wt2= do
     -- check in and out dists are same
     assertM (return $ match parD1 [parD1, mirD2, parD3]) "par/mirr dims don't match"
     --assertM (return $ match mirD1 [mirD2, mirD3]) "mirror dims don't match"
     -- get input var names 
     getVar (Tup [Lf "k1", Lf "v1"]) inN1 "streamVar"
     getVar (Lf "inV2") inN2 outVarName
     -- declare loop iterator and end iterator
     (TyV treeMapTy) <- getVal inN2 "treeMapTy"
     let iterTy = Lf $ LfTy "ConstIter" [treeMapTy]
     newVar (Lf "it2") iterTy
     newVar (Lf "end2") iterTy 
     varExp "itBegin2" "inV2" "<v>->csbegin()" iterTy
     varExp "itEnd2" "inV2" "<v>->csend()" iterTy
     runGenV "declareVarInit" "decIt2" [Lf "it2", Lf "itBegin2"]
     runGenV "declareVarInit" "decEnd2" [Lf "end2", Lf "itEnd2"]
     -- declare stream var
     varExp "i2" "it2" "<v>->v0" ity1
     varExp "w2" "it2" "<v>->v1" wt1
     setVar outN "streamVar" $ Tup [Tup [Lf "k1", Lf "i2"], Tup [Lf "v1", Lf "w2"]]
     -- if we know the maps sizes, pass it on
     ifVarExists "count1" inN1 "count" (
       ifVarExists "count2" inN2 "count" (do
           countExp <- expandTem "crossVMaps11:countExp:" "(<count1>) * (<count2>)" ;
           varExp "count" "" countExp intTy ;
           setVar outN "count" $ Lf "count"
         ) (return ())) (return ())
     -- when gen is called, generate loop
     setFun outN "genConsumers" nt (\_ -> do
       -- gen consumers
       callAll outN "genConsumers" nt
       ifVarsExist [("init", outN, "initStream"), ("fin", outN, "finStream"), ("consume", outN, "consumers")] (do
         -- local data pred
         genHasDataPred "hasData" parD2 mirD2
         -- output code
         addCode inN1 "initStream" "// begin <tem> init\n<init>\n// end <tem> init\n"
         addCode inN1 "consumers" $ 
           "// BEGIN <tem> consume:\n"++
           "if (<hasData>) {\n"++
           "  <decIt2><decEnd2>\n"++
           "  for (; <it2> != <end2>; <it2>++) {\n"++
           "    <consume>\n"++
           "  }\n"++
           "}\n"++
           "// END <tem> consume\n"
         addCode inN1 "finStream" "<fin>"
         ) (return ())
       return ())
t07 t n = terr' t n

-- |unionVMaps1 template
t09 :: (Monad m, MonadCatch m) => Template m
t09 (Tup [Lf (LfTy "DMap" [mode1, kt1, vt1, ordF1, parF1, parD1, mirD1]),
          Lf (LfTy "DMap" [mode2, kt2, vt2, ordF2, parF2, parD2, mirD2])] :-> 
     Lf (LfTy "DMap" [mode3, kt3, vt3, ordF3, parF3, parD3, mirD3]))
   (LFun _ (LTup _ [inN1, inN2]) outN)
   | mode1 == nameTy "Stm" && mode2 == nameTy "Vec" && mode3 == nameTy "Stm" &&
     match kt1 [kt2,kt3] && match vt1 [vt2, vt3] = do
     -- check in and out dists are same
     assertM (return $ match parD1 [parD2, parD3]) "par dims don't match"
     assertM (return $ match mirD1 [mirD2, mirD3]) "mirror dims don't match"
     -- get input var names 
     getVar (Tup [Lf "k1", Lf "v1"]) inN1 "streamVar"
     getVar (Lf "inV2") inN2 outVarName
     -- declare loop iterator and end iterator
     (TyV treeMapTy) <- getVal inN2 "treeMapTy"
     let iterTy = Lf $ LfTy "ConstIter" [treeMapTy]
     newVar (Lf "it2") iterTy
     newVar (Lf "end2") iterTy 
     varExp "itBegin2" "inV2" "<v>->cpbegin()" iterTy
     varExp "itEnd2" "inV2" "<v>->cpend()" iterTy
     runGenV "declareVarInit" "decIt2" [Lf "it2", Lf "itBegin2"]
     runGenV "declareVarInit" "decEnd2" [Lf "end2", Lf "itEnd2"]
     varExp "k2" "it2" "<v>->v0" kt1
     varExp "v2" "it2" "<v>->v1" vt1
     -- declare comparisons
     runGenV "ltVar" "pred1Lt2" [Lf "k1", Lf "k2"]
     runGenV "ltVar" "pred2Lt1" [Lf "k2", Lf "k1"]
     runGenV "eqVar" "pred1Eq2" [Lf "k1", Lf "k2"]
     -- declare stream var
     newVar (Tup [Lf "outK", Lf "outV"]) $ Tup [kt1, vt1]
     runGenV "assignVar" "copy1" [Tup [Lf "outK", Lf "outV"], Tup [Lf "k1", Lf "v1"]] 
     runGenV "assignVar" "copy2" [Tup [Lf "outK", Lf "outV"], Tup [Lf "k2", Lf "v2"]] 
     setVar outN "streamVar" $ Tup [Lf "outK", Lf "outV"]
     runGenV "declareVar" "decOut" [Tup [Lf "outK", Lf "outV"]]
     -- we can't know the result count, so can't pass it on
     -- when gen is called, generate loop
     setFun outN "genConsumers" nt (\_ -> do
       -- gen consumers (TODO could we call genConsumers twice, with different stream vars???)
       callAll outN "genConsumers" nt
       ifVarsExist [("init", outN, "initStream"), ("fin", outN, "finStream"), ("consume", outN, "consumers")] (do
         -- output code
         addCode inN1 "initStream" "// begin <tem> init\n<init><decIt2><decEnd2><decOut>// end <tem> init\n"
         addCode inN1 "consumers" $ 
           "// BEGIN <tem> consume:\n"++
           "while (<it2> != <end2> && (<pred2Lt1>)) {\n"++
           "  // emit 2, inc 2\n"++
           "  <copy2>\n<consume>\n<it2>++;\n"++
           "}\n"++
           "// emit 1, inc 1\n"++
           "<copy1>\n<consume>\n"++
           "if (<it2> != <end2> && (<pred1Eq2>)) { // inc 2 aswell\n"++
           "  <it2>++;\n"++
           "}\n"++        
           "// END <tem> consume\n"
         addCode inN1 "finStream" $ 
           "// BEGIN <tem> fin\n"++
           "// emit any vals remaining from input 2\n"++
           "while (<it2> != <end2>) {\n"++
           "  // emit val from input 2, and progress input 2\n"++
           "  <copy2>\n<consume>\n<it2>++;\n"++
           "}\n"++
           "<fin>\n"++
           "// END <tem> fin\n"
         ) (do output "main" "// <tem> not used so not generated.\n"; return ())
       return ())
t09 t n = terr' t n

-- |unionVMaps3 template
t13 :: (Monad m, MonadCatch m) => Template m
t13 (Tup [Lf (LfTy "DMap" [mode1, kt1, vt1, ordF1, parF1, parD1, mirD1]),
          Lf (LfTy "DMap" [mode2, kt2, vt2, ordF2, parF2, parD2, mirD2])] :-> 
     Lf (LfTy "DMap" [mode3, kt3, vt3, ordF3, parF3, parD3, mirD3]))
   (LFun _ (LTup _ [inN1, inN2]) outN)
   | mode1 == nameTy "Vec" && mode2 == nameTy "Stm" && mode3 == nameTy "Stm" &&
     match kt1 [kt2,kt3] && match vt1 [vt2, vt3] = do
     -- check in and out dists are same
     assertM (return $ match parD1 [parD2, parD3]) "par dims don't match"
     assertM (return $ match mirD1 [mirD2, mirD3]) "mirror dims don't match"
     -- get input var names 
     getVar (Tup [Lf "k2", Lf "v2"]) inN2 "streamVar"
     getVar (Lf "inV1") inN1 outVarName
     -- declare loop iterator and end iterator
     (TyV treeMapTy) <- getVal inN1 "treeMapTy"
     let iterTy = Lf $ LfTy "ConstIter" [treeMapTy]
     newVar (Lf "it1") iterTy
     newVar (Lf "end1") iterTy 
     varExp "itBegin1" "inV1" "<v>->cpbegin()" iterTy
     varExp "itEnd1" "inV1" "<v>->cpend()" iterTy
     runGenV "declareVarInit" "decIt1" [Lf "it1", Lf "itBegin1"]
     runGenV "declareVarInit" "decEnd1" [Lf "end1", Lf "itEnd1"]
     varExp "k1" "it1" "<v>->v0" kt1
     varExp "v1" "it1" "<v>->v1" vt1
     -- declare comparisons
     runGenV "ltVar" "pred2Lt1" [Lf "k2", Lf "k1"]
     runGenV "ltVar" "pred1Lt2" [Lf "k1", Lf "k2"]
     runGenV "eqVar" "pred1Eq2" [Lf "k2", Lf "k1"]
     -- declare stream var
     newVar (Tup [Lf "outK", Lf "outV"]) $ Tup [kt1, vt1]
     runGenV "assignVar" "copy1" [Tup [Lf "outK", Lf "outV"], Tup [Lf "k1", Lf "v1"]] 
     runGenV "assignVar" "copy2" [Tup [Lf "outK", Lf "outV"], Tup [Lf "k2", Lf "v2"]] 
     setVar outN "streamVar" $ Tup [Lf "outK", Lf "outV"]
     runGenV "declareVar" "decOut" [Tup [Lf "outK", Lf "outV"]]
     -- we can't know the result count, so can't pass it on
     -- when gen is called, generate loop
     setFun outN "genConsumers" nt (\_ -> do
       -- gen consumers (TODO could we call genConsumers twice, with different stream vars???)
       callAll outN "genConsumers" nt
       ifVarsExist [("init", outN, "initStream"), ("fin", outN, "finStream"), ("consume", outN, "consumers")] (do
         -- output code
         addCode inN1 "initStream" "// begin <tem> init\n<init><decIt1><decEnd1><decOut>// end <tem> init\n"
         addCode inN1 "consumers" $ 
           "// BEGIN <tem> consume:\n"++
           "while (<it1> != <end1> && (<pred1Lt2>)) {\n"++
           "  // emit 1, inc 1\n"++
           "  <copy1>\n<consume>\n<it1>++;\n"++
           "}\n"++
           "// emit 2, inc 2\n"++
           "<copy2>\n<consume>\n"++
           "if (<it1> != <end1> && (<pred1Eq2>)) { // inc 1 aswell\n"++
           "  <it1>++;\n"++
           "}\n"++        
           "// END <tem> consume\n"
         addCode inN1 "finStream" $ 
           "// BEGIN <tem> fin\n"++
           "// emit any vals remaining from input 2\n"++
           "while (<it1> != <end1>) {\n"++
           "  // emit val from input 2, and progress input 2\n"++
           "  <copy1>\n<consume>\n<it1>++;\n"++
           "}\n"++
           "<fin>\n"++
           "// END <tem> fin\n"
         ) (do output "main" "// <tem> not used so not generated.\n"; return ())
       return ())
t13 t n = terr' t n

-- |unionVMaps2 template
t10 :: (Monad m, MonadCatch m) => Template m
t10 (Tup [Lf (LfTy "DMap" [mode1, kt1, vt1, ordF1, parF1, parD1, mirD1]),
          Lf (LfTy "DMap" [mode2, kt2, vt2, ordF2, parF2, parD2, mirD2])] :-> 
     Lf (LfTy "DMap" [mode3, kt3, vt3, ordF3, parF3, parD3, mirD3]))
   (LFun _ (LTup _ [inN1, inN2]) outN)
   | mode1 == nameTy "Vec" && mode2 == nameTy "Vec" && mode3 == nameTy "Vec" &&
     match kt1 [kt2,kt3] && match vt1 [vt2, vt3] = do
     -- check in and out dists are same
     assertM (return $ match parD1 [parD2, parD3]) "par dims don't match"
     assertM (return $ match mirD1 [mirD2, mirD3]) "mirror dims don't match"
     -- get input var names 
     getVar (Lf "inV1") inN1 outVarName
     getVar (Lf "inV2") inN2 outVarName
     -- declare output vecmap
     (TyV vecmapTy) <- getVal inN2 "treeMapTy"
     setVal outN "treeMapTy" (TyV vecmapTy) -- pass vecmap type to out
     tn <- getTemplateName
     vecmapTyName <- genTypeName vecmapTy >>= (return . (fromMaybe (error $ "Templates:" ++ tn ++ " can't get type name of " ++ (show vecmapTy))))
     varExp "size1" "inV1" "<v>->size()" intTy
     varExp "size2" "inV2" "<v>->size()" intTy
     varExp "newTreeMap" "" ("new " ++ vecmapTyName ++ "(<size1>+<size2>)") (Lf $ LfTy "Ptr" [vecmapTy])
     ifnVarInit "decOut" outVarName (Lf "outMap") (Lf $ LfTy "SPtr" [vecmapTy]) (Just $ Tup [Lf "newTreeMap"]) 
     -- declare loop iterator and end iterator
     let iterTy = Lf $ LfTy "ConstIter" [vecmapTy]
     newVar (Lf "resIt") iterTy
     runGenV "declareVar" "decResIt" [Lf "resIt"]
     newVar (Lf "outBegin") iterTy
     runGenV "declareVar" "decOutBegin" [Lf "outBegin"]
     varExp "itBegin2" "inV2" "<v>->cpbegin()" iterTy
     varExp "itEnd2" "inV2" "<v>->cpend()" iterTy
     -- we can't know the result count, so can't pass it on
     -- generate code
     setFun outN "gen" nt (\_ -> do
       outputDecl outN "// begin <tem> decl\n<decOut>\n// end <tem> decl\n"
       output "main" $
         "<decResIt>\n<decOutBegin>\n"++
         "<outBegin> = <outMap>->cpbegin();\n "++ 
         "<resIt> = <inV1>->setUnion(<inV2>->cpbegin(), <inV2>->cpend(), <outBegin>);\n"++
         "<outMap>->resize(<resIt>-<outBegin>); // reduce size to whats needed for union\n" 
       return ())
t10 t n = terr' t n-}

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
module Compiler.Back.Maps.STemplates where

import Data.Maybe (fromMaybe)
import Control.Monad.State.Strict (gets)
import Control.Monad.Catch

import Compiler.Back.Graph
import Compiler.Back.GenDecls
import Compiler.Back.Gen
import Compiler.Back.Generators
import Compiler.Back.Templates
import Compiler.Back.Helper
import Compiler.Back.CartTopology


-- stream map templates

smapTemplates :: (Monad m, MonadCatch m) => [(Id, Template m)]
smapTemplates = [
  ("genFloatSMap", t01),
  ("mapSMap1", t02),
  ("mapSMap2", t02),
  ("mapSMapVals1", t10),
  ("mapSMapVals2", t10),
  ("reduceSMap", t03),
  ("groupReduceSMap", t04),
  ("printSMap", t05),
  ("intRangeSMap1", t06),
  ("intRangeSMap2", t08),
  ("intRangeSMapMirr", t07),
  ("emptySMap", t09),
  ("sieveSMap", t11)
  ]

-- |genFloatSMap template
t01 :: (Monad m, MonadCatch m) => Template m
t01 (t1 :-> (Lf (LfTy "DMap" [mode, keyT, valT, ordF, parF, parD, mirD])))
   (LFun _ inN outN)
   | t1 == intTy && mode == nameTy "Stm" &&
     keyT == intTy && valT == floatTy = do
     -- declare stream var
     newVar (Lf "floatV") floatTy
     newVar (Lf "intV") intTy
     newVar (Lf "start") intTy
     setVar outN "streamVar" $ Tup [Lf "intV", Lf "floatV"]
     -- since we know the map's size, pass it on
     newVar (Lf "localSz") intTy
     getVar (Lf "sz") inN outVarName
     setVar outN "count" $ Lf "sz"
     -- when gen is called, generate loop
     setFun outN "gen" nt (\_ -> do
       -- gen consumers
       callAll outN "genConsumers" nt
       ifVarsExist [("init", outN, "initStream"), ("fin", outN, "finStream"), ("consume", outN, "consumers")] (do
         -- local data pred
         genHasDataPred "hasData" parD mirD
         -- output code
         outMain $
           "<init>\n"++
           "if (<hasData>) {\n" ++
           "int <localSz> = (<sz> / Nproc) + (thisRank < (<sz> % Nproc) ? 1 : 0);\n"++
           "int <start> = 0;\n"++
           "for (int <intV> = 0; <intV> < thisRank; <intV>++) <start> += (<sz> / Nproc) + (<intV> < (<sz> % Nproc) ? 1 : 0);\n"++
           "for (int <intV> = <start>; <intV> < <start>+<localSz>; <intV>++) {\n"++
           "  double <floatV> = (double)rand() / RAND_MAX;\n"++
           "  <consume>\n"++
           "}\n"++
           "}\n"++
           "<fin>\n"
         ) (return ())
       return ())
t01 t n = terr' t n

-- |mapSMap template
t02 :: (Monad m, MonadCatch m) => Template m
t02 (Tup [((Tup [kt1, vt1]) :-> (Tup [kt2, vt2])), 
          (Lf (LfTy "DMap" [mode1, keyT1, valT1, ordF1, parF1, parD1, mirD1]))] :-> 
          (Lf (LfTy "DMap" [mode2, keyT2, valT2, ordF2, parF2, parD2, mirD2])))
   (LFun _ (LTup _ [funN, inN]) outN)
   | kt1 == keyT1 && vt1 == valT1 && kt2 == keyT2 && vt2 == valT2 && 
     mode1 == nameTy "Stm" && mode2 == nameTy "Stm" = do
     -- check in and out dims are the same
     assertM (return $ parD1 == parD2) $ "par dims don't match"
     assertM (return $ mirD1 == mirD2) $ "mirror dims don't match"
     -- get input stream vars
     getVar (Tup [Lf "k1", Lf "v1"]) inN "streamVar"
     -- declare and set output stream vars
     newVar (Tup [Lf "k2", Lf "v2"]) (Tup [kt2, vt2])
     runGenV "declareVar" "decStmVar" [Tup [Lf "k2", Lf "v2"]]
     setVar outN "streamVar" $ Tup [Lf "k2", Lf "v2"]
     -- if we know the maps size, pass it on
     ifVarExists "count" inN "count" (setVar outN "count" $ Lf "count") (return ())
     -- when gen is called, generate loop
     setFun outN "genConsumers" nt (\_ -> do
       -- generate map fun implementation
       genFunV "funCode" funN (Tup [Lf "k1", Lf "v1"]) n0 (Tup [Lf "k2", Lf "v2"])
       -- gen consumers
       callAll outN "genConsumers" nt
       -- add these consumers to producer
       ifVarsExist [("init", outN, "initStream"), ("fin", outN, "finStream"), ("consume", outN, "consumers")] (do
         addCode inN "consumers" $ "// BEGIN <tem> consume:\n<decStmVar><funCode>\n<consume>\n// END <tem> consume\n"
         addCode inN "initStream" "<init>"
         addCode inN "finStream" "<fin>"
         ) (return ())
       return ())
t02 t n = terr' t n

-- |mapSMapVals template
t10 :: (Monad m, MonadCatch m) => Template m
t10 (Tup [(vt1 :-> vt2), 
          (Lf (LfTy "DMap" [mode1, keyT1, valT1, ordF1, parF1, parD1, mirD1]))] :-> 
          (Lf (LfTy "DMap" [mode2, keyT2, valT2, ordF2, parF2, parD2, mirD2])))
   (LFun _ (LTup _ [funN, inN]) outN)
   | keyT1 == keyT2 && vt1 == valT1 && vt2 == valT2 && 
     mode1 == nameTy "Stm" && mode2 == nameTy "Stm" = do
     -- check in and out dims are the same
     assertM (return $ parD1 == parD2) $ "par dims don't match"
     assertM (return $ mirD1 == mirD2) $ "mirror dims don't match"
     -- get input stream vars
     getVar (Tup [Lf "k1", Lf "v1"]) inN "streamVar"
     -- declare and set output stream vars
     newVar (Lf "v2") vt2
     runGenV "declareVar" "decStmVar" [Lf "v2"]
     setVar outN "streamVar" $ Tup [Lf "k1", Lf "v2"]
     -- if we know the maps size, pass it on
     ifVarExists "count" inN "count" (setVar outN "count" $ Lf "count") (return ())
     -- when gen is called, generate loop
     setFun outN "genConsumers" nt (\_ -> do
       -- generate map fun implementation
       genFunV "funCode" funN (Lf "v1") n0 (Lf "v2")
       -- gen consumers
       callAll outN "genConsumers" nt
       -- add these consumers to producer
       ifVarsExist [("init", outN, "initStream"), ("fin", outN, "finStream"), ("consume", outN, "consumers")] (do
         addCode inN "consumers" $ "// BEGIN <tem> consume:\n<decStmVar><funCode>\n<consume>\n// END <tem> consume\n"
         addCode inN "initStream" "<init>"
         addCode inN "finStream" "<fin>"
         ) (return ())
       return ())
t10 t n = terr' t n

-- |reduceSMap template
t03 :: (Monad m, MonadCatch m) => Template m
t03 (Tup [Tup [kt1, vt1] :-> st1, Tup [st2, st3] :-> st4, st6,
          Lf (LfTy "DMap" [mode1, kt2, vt2, ordF1, parF1, parD1, mirD1])] :-> st5)
   (LFun _ (LTup _ [funN1, funN2, val0N, inN]) outN)
   | kt1 == kt2 && vt1 == vt2 && match st1 [st2, st3, st4, st5, st6] &&
     mode1 == nameTy "Stm" = do
     -- get input vars
     getVar (Tup [Lf "key", Lf "val"]) inN "streamVar"
     getVar (Lf "v0") val0N outVarName
     -- declare output var
     ifnVar "decOut" outVarName (Lf "st1") st1
     -- declare temp vars
     newStructVar (Lf "acc") st1
     newStructVar (Lf "st2") st1
     runGenV "declareVar" "decVars" [Tup [Lf "st2", Lf "acc"]]
     -- apply functions 
     genFunV "appProj" funN1 (Tup [Lf "key", Lf "val"]) val0N (Lf "st1")
     genFunV "appCombine1" funN2 (Tup [Lf "st1", Lf "acc"]) n0 (Lf "st2")
     runGenV "assignVar" "appCopy" [Lf "acc", Lf "st2"] 
     runGenV "assignVar" "appInit" [Lf "acc", Lf "v0"] 
     runGenV "assignVar" "copySt" [Lf "st1", Lf "st2"]
     -- declare AllReduce Op
     combineFun <- getFun funN2
     genTrace "reduceDStream:got combineFun"
     runGen "reduceFun" "redFunName" [TyV st1, combineFun]
     genTrace "reduceDStream:generated reduceFun"
     newVar (Lf "redOp") intTy
     output "decls" "MPI::Op <redOp>;\n\n"
     output "init" "<redOp>.Init(&<redFunName>, true);\n\n"
     -- when gen is called, generate redist code
     setFun outN "genConsumers" nt (\_ -> do
       -- prep for allreduce
       resTyNameMb <- genTypeName st1
       tn <- getTemplateName
       let resTyName = fromMaybe (error $ tn ++ ": can't get result type name!") resTyNameMb
       setLocalVal "resTyName" $ IdV resTyName
       -- local data for this dist
       genHasDataPred "hasData" parD1 mirD1
       genSubCartV "localComm" "localRanks" parD1
       -- add consumers to producer
       outputDecl outN "<decOut>"
       addCode inN "initStream" $ 
         "// BEGIN <tem> init\n<decVars><appInit>\n"++ -- <decOut>
         "// END <tem> init\n"
       addCode inN "consumers" $ 
         "// BEGIN <tem> consume\n"++
         "  <appProj><appCombine1><appCopy>\n"++
         "// END <tem> consume\n"
       addCode inN "finStream" $ 
         -- reduce among nodes that have data
         "// BEGIN <tem> fin\n"++
         "if (<hasData>) {\n"++
         "  <localComm>.Allreduce(&<acc>, &<st2>, sizeof(<resTyName>), MPI::BYTE, <redOp>);\n"++
         "  <copySt>\n"++
         "}\n"++
         -- if local comm isn't the global one, broadcast to any remaining ones 
         "if (<localComm> != cartComm) {\n"++
         "  cartComm.Bcast(&<st2>, sizeof(<resTyName>), MPI::BYTE, rootRank);\n" ++
         "}\n"++
         "// END <tem> fin\n"
       return ())
t03 t n = terr' t n

-- |groupReduceSMap template
t04 :: (Monad m, MonadCatch m) => Template m
t04 (Tup [Tup [kt1, vt1] :-> ity1,
         Tup [kt2, vt2] :-> wt1,
         Tup [wt2, wt3] :-> wt4,
         wt5, 
         inTy@(Lf (LfTy "DMap" [mode1, kt3, vt3, of1, pf1, d1, m1]))] :-> 
         outT@(Lf (LfTy "DMap" [mode2, ity2, wt6, of2, pf2, d2, m2])))
   (LFun _ (LTup _ [kfN, vfN, rfN, w0N, inN]) outN) 
   | match kt1 [kt2,kt3] && match vt1 [vt2,vt3] && ity1 == ity2 &&
     match wt1 [wt2,wt3,wt4,wt5,wt6] && 
     match (nameTy "Stm") [mode1, mode2] = do
     tn <- getTemplateName
     -- sanity check
     -- check in and out dims are the same
     assertM (return $ d1 == d2) "par dims don't match"
     assertM (return $ m1 == m2) "mirror dims don't match"
     -- create new key and new val vars
     newVar (Lf "newK") ity1
     newVar (Lf "oldK") ity1
     newVar (Lf "newV") wt1
     newVar (Lf "accV") wt1
     newVar (Lf "tmpV") wt1
     newVar (Lf "firstEl") boolTy
     -- get inputs vars
     getVar (Tup [Lf "key1", Lf "val1"]) inN "streamVar"
     getVar (Lf "w0") w0N outVarName
     genTrace "get w0 done"
     -- set output vars
     setVar outN "streamVar" $ Tup [Lf "oldK", Lf "accV"]
     -- def "genConsumers" to generate print statements
     setFun outN "genConsumers" nt (\_ -> do
       curNid <- gets genCurrentNode
       genTrace $ "entered " ++ tn ++ ".genConsumers: " ++ (show curNid) ++ "\n"
       -- declare vars
       runGenV "declareVar" "decVars" [Tup [Lf "newK", Lf "oldK", Lf "newV", Lf "accV"]]
       runGenV "declareVar" "decTmpV" [Lf "tmpV"]
       -- generate code to get new key and new val
       genFunV "getNewKey" kfN (Tup [Lf "key1", Lf "val1"]) n0 (Lf "newK")
       genFunV "getNewVal" vfN (Tup [Lf "key1", Lf "val1"]) w0N (Lf "newV")
       genFunV "combineVals" rfN (Tup [Lf "accV", Lf "newV"]) n0 (Lf "tmpV")
       runGenV "assignVar" "copyKey" [Lf "oldK", Lf "newK"] 
       runGenV "assignVar" "copyAcc" [Lf "accV", Lf "tmpV"] 
       runGenV "assignVar" "initAcc" [Lf "accV", Lf "w0"] 
       runGenV "eqVar" "cmpKeys" [Lf "newK", Lf "oldK"]
       -- gen consumers
       callAll outN "genConsumers" nt
       -- add blocks to consumers
       beginMsg <- temMsg "begin consumer"
       endMsg <- temMsg "end consumer"
       ifVarsExist [("init", outN, "initStream"), ("fin", outN, "finStream"), ("consume", outN, "consumers")] (do
         addCode inN "initStream" "<init><decVars><initAcc>\nbool <firstEl> = true;"
         addCode inN "consumers" $ "// begin <tem> consume\n" ++ --beginMsg ++
           -- proj key
           "<getNewKey>\n" ++
           -- if key has changed
           "if (!(<cmpKeys>)) {\n"++
             -- if first element then, don't consume (since they first oldK value will be arbitrary/undefined)
           "  if (<firstEl>) { }\n"++
             -- else, call consumer with current val and old key, and then set val to default val ready for next key
           "  else { <consume><initAcc> }\n"++
             -- set old key to new key 
           "  <copyKey>"++
           "}\n"++
           -- project out new val, and combine with acc
           "<getNewVal>\n" ++
           "<decTmpV>\n"++
           "<combineVals>\n" ++
           "<copyAcc>\n" ++ 
           "<firstEl> = false;\n"++
           "// begin <tem> consume\n" -- ++ endMsg
         addCode inN "finStream" $
           -- if one or more elements then consume's last value
           "if (!<firstEl>) {\n<consume>\n}\n"++
           "<fin>"
         ) (return ())
       )
t04 t n = terr' t n

-- |printSMap template
t05 :: (Monad m, MonadCatch m) => Template m
t05 (Lf (LfTy "DMap" [mode1, keyT1, valT1, ordF1, parF1, parD1, mirD1]) :-> nullT)
   (LFun _ inN outN)
   | mode1 == nameTy "Stm" = do
     -- get input stream vars
     getVar (Lf "sval") inN "streamVar"
     -- pack in struct to print
     newStructVar (Lf "val") $ Tup [keyT1, valT1]
     runGenV "declareVar" "decVal" [Lf "val"]
     runGenV "assignVar" "packVal" [Lf "val", Lf "sval"] 
     -- generate print consumer
     setFun outN "genConsumers" nt (\_ -> do
       -- add these consumers to producer
       addCode inN "consumers" $ "// BEGIN <tem> consume:\n<packVal>\nprintVal(<val>); printVal(\"\\n\");\n// END <tem> consume\n"
       addCode inN "initStream" "<decVal>\n" -- if (thisRank == rootRank) printVal(\"[\");\n"
       addCode inN "finStream" "" -- "if (thisRank == rootRank) printVal(\"]\");\n"
       return ())
t05 t n = terr' t n

-- |intRangeSMap1 template -- iterate through whole range, filtering using the partition function
t06 :: (Monad m, MonadCatch m) => Template m
t06 (Tup [int1, int2, int3] :-> (Lf (LfTy "DMap" [mode, keyT, valT, ordF, parF, parD, mirD])))
   (LFun _ (LTup _ [fstN, lstN, stepN]) outN)
   | mode == nameTy "Stm" &&
     match intTy [keyT,int1,int2,int3] && valT == nullTy = do
     -- get input vars
     getVar (Lf "fstV") fstN outVarName
     getVar (Lf "lstV") lstN outVarName
     getVar (Lf "stepV") stepN outVarName
     -- declare stream var
     newVar (Lf "intK") intTy
     newVar (Lf "nullV") nullTy
     setVar outN "streamVar" $ Tup [Lf "intK", Lf "nullV"]
     -- get rank ints belong on
     newVar (Lf "rank") intTy
     runGenV "declareVar" "decRank" [Lf "rank"]
     genSubCartV "localComm" "localRanks" parD
     varToNodeRankV "getRank" (Lf "intK") "rank" parD parD mirD
     -- when gen is called, generate loop
     setFun outN "gen" nt (\_ -> do
       -- gen consumers
       callAll outN "genConsumers" nt
       ifVarsExist [("init", outN, "initStream"), ("fin", outN, "finStream"), ("consume", outN, "consumers")] (do
         -- local data pred
         genHasDataPred "hasData" parD mirD
         -- output code
         beginMsg <- temMsg "begin producer"
         endMsg <- temMsg "end producer"
         outMain $ beginMsg ++
           "<init>\n"++
           "if (<hasData>) {\n" ++
           "for (int <intK> = <fstV>; <intK> <= <lstV>; <intK> += <stepV>) {\n"++
           "  // get rank that this int belong on\n"++
           "  <decRank>\n<getRank>\n"++
           "  // consume if this int belongs here\n"++
           "  if (thisRank == <rank>) {"++
           "    <consume>\n"++
           "  }\n"++
           "}\n"++
           "}\n"++
           "<fin>\n" ++ endMsg
         ) (return ())
       return ())
t06 t n = terr' t n

-- TODO block partition this...
-- |intRangeSMap2 template -- iterate through whole range, partitioned into blocks
t08 :: (Monad m, MonadCatch m) => Template m
t08 (Tup [int1, int2, int3] :-> (Lf (LfTy "DMap" [mode, keyT, valT, ordF, parF, parD, mirD])))
   (LFun _ (LTup _ [fstN, lstN, stepN]) outN)
   | mode == nameTy "Stm" &&
     match intTy [keyT,int1,int2,int3] && valT == nullTy = do
     -- get input vars
     getVar (Lf "fstV") fstN outVarName
     getVar (Lf "lstV") lstN outVarName
     getVar (Lf "stepV") stepN outVarName
     -- declare stream var
     newVar (Lf "intK") intTy
     newVar (Lf "nullV") nullTy
     setVar outN "streamVar" $ Tup [Lf "intK", Lf "nullV"]
     -- vars for current block
     newVar (Lf "blkCount") intTy
     newVar (Lf "blkRank") intTy
     newVar (Lf "blkRange") intTy
     genSubCartV "localComm" "localRanks" parD
     -- when gen is called, generate loop
     setFun outN "gen" nt (\_ -> do
       -- gen consumers
       callAll outN "genConsumers" nt
       ifVarsExist [("init", outN, "initStream"), ("fin", outN, "finStream"), ("consume", outN, "consumers")] (do
         -- local data pred
         genHasDataPred "hasData" parD mirD
         -- output code
         beginMsg <- temMsg "begin producer"
         endMsg <- temMsg "end producer"
         outMain $ beginMsg ++
           "<init>\n"++
           "if (<hasData>) {\n" ++
           "int <blkCount> = <localComm>.Get_size();\n" ++
           "int <blkRank> = <localComm>.Get_rank();\n"++
           "intPair <blkRange> = partitionIntRange(<fstV>, <lstV>, <stepV>, <blkCount>, <blkRank>);\n"++
           "#ifdef DEBUG\n"++
           "std::cout << thisRank << \") intRangeSMap2: \" << <blkRange>.v0 << \" to \" << <blkRange>.v1 << \"\\n\";\n"++
           "#endif\n"++
           "for (int <intK> = <blkRange>.v0; <intK> < <blkRange>.v1; <intK> += <stepV>) {\n"++
           "  <consume>\n"++
           "}\n"++
           "}\n"++
           "<fin>\n" ++ endMsg
         ) (return ())
       return ())
t08 t n = terr' t n

-- FIX THIS

-- |intRangeSMapMirr template -- iterate through whole range mirrored
t07 :: (Monad m, MonadCatch m) => Template m
t07 (Tup [int1, int2, int3] :-> (Lf (LfTy "DMap" [mode, keyT, valT, ordF, parF, parD, mirD])))
   (LFun _ (LTup _ [fstN, lstN, stepN]) outN)
   | mode == nameTy "Stm" && parD == nullTy &&
     match intTy [keyT,int1,int2,int3] && valT == nullTy = do
     -- get input vars
     getVar (Lf "fstV") fstN outVarName
     getVar (Lf "lstV") lstN outVarName
     getVar (Lf "stepV") stepN outVarName
     -- declare stream var
     newVar (Lf "intK") intTy
     newVar (Lf "nullV") nullTy
     setVar outN "streamVar" $ Tup [Lf "intK", Lf "nullV"]
     -- when gen is called, generate loop
     setFun outN "gen" nt (\_ -> do
       -- gen consumers
       callAll outN "genConsumers" nt
       ifVarsExist [("init", outN, "initStream"), ("fin", outN, "finStream"), ("consume", outN, "consumers")] (do
         -- local data pred
         genHasDataPred "hasData" parD mirD
         -- output code
         beginMsg <- temMsg "begin producer"
         endMsg <- temMsg "end producer"
         outMain $ beginMsg ++
           "<init>\n"++
           "if (<hasData>) {\n" ++
           "for (int <intK> = <fstV>; <intK> <= <lstV>; <intK> += <stepV>) {\n"++
           "  <consume>\n"++
           "}\n"++
           "}\n"++
           "<fin>\n" ++ endMsg
         ) (return ())
       return ())
t07 t n = terr' t n

-- |emptySMap template
t09 :: (Monad m, MonadCatch m) => Template m
t09 (t1 :-> (Lf (LfTy "DMap" [mode, keyT, valT, ordF, parF, parD, mirD])))
   (LFun _ inN outN)
   | mode == nameTy "Stm" = do
     -- declare stream var
     newVar (Lf "key") keyT
     newVar (Lf "val") valT
     setVar outN "streamVar" $ Tup [Lf "key", Lf "val"]
     -- since we know the map's size, pass it on
     varExp "sz" "" "0" intTy
     setVar outN "count" $ Lf "sz"
     -- when gen is called, generate loop
     setFun outN "gen" nt (\_ -> do
       -- gen consumers
       callAll outN "genConsumers" nt
       ifVarsExist [("init", outN, "initStream"), ("fin", outN, "finStream"), ("consume", outN, "consumers")] (do
         -- output code
         outMain $ "// begin <tem>\n" ++ 
           "<init>\n<fin>\n" ++
           "// end <tem>\n"
         ) (return ())
       return ())
t09 t n = terr' t n

-- |sieveSMap template
t11 :: (Monad m, MonadCatch m) => Template m
t11 ((Lf (LfTy "DMap" [mode1, keyT1, valT1, ordF1, parF1, parD1, mirD1])) :-> 
     (Lf (LfTy "DMap" [mode2, keyT2, valT2, ordF2, parF2@(Lf (FunTy parG)), parD2, mirD2])))
   (LFun _ inN outN)
   | keyT1 == keyT2 && valT1 == valT2 && 
     mode1 == nameTy "Stm" && mode2 == nameTy "Stm" = do
     -- check in and out dims are the same
     assertM (return $ mirD1 == parD2) $ "domain mirror dim doesn't equal range partition dim!"
     assertM (return $ parD1 == nullTy) $ "domain partition dim isn't null!"
     assertM (return $ mirD2 == nullTy) $ "range mirror dim isn't null!"
     -- get input stream vars
     getVar (Lf "svar") inN "streamVar"
     setVar outN "streamVar" $ Lf "svar"
     -- (can't pass on map size)
     -- create local cart comm
     genSubCartV "localComm" "localRanks" parD2
     varExp "localCommPtr" "localComm" "&(<v>)" intTy
     -- make partition function application
     (parInTy :-> parOutTy)  <- getGraphTy parG
     newVar (Lf "pval") parOutTy
     runGenV "declareVar" "decPval" [Lf "pval"]
     genTyFunV "appPf" parF2 (Lf "svar") n0 (Lf "pval")
     newVar (Lf "rank") intTy
     runGenV "declareVar" "decRank" [Lf "rank"]
     varToNodeRankV "getRank" (Lf "pval") "rank" parD2 parD2 mirD2
     -- when gen is called, generate loop
     setFun outN "genConsumers" nt (\_ -> do
       -- gen consumers
       callAll outN "genConsumers" nt
       -- add these consumers to producer
       ifVarsExist [("init", outN, "initStream"), ("fin", outN, "finStream"), ("consume", outN, "consumers")] (do
         addCode inN "initStream" "<init><decPval><decRank>"
         addCode inN "consumers" $ 
           "// BEGIN <tem> consume:\n"++
           "<appPf><getRank>\n"++
           "if (thisRank == <rank>) {\n"++
           "  <consume>\n"++
           "}\n"++
           "// END <tem> consume\n"
         addCode inN "finStream" "<fin>"
         ) (return ())
       return ())
t11 t n = terr' t n


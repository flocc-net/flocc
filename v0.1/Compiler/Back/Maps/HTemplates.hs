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
module Compiler.Back.Maps.HTemplates where

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

import Compiler.Back.Maps.VTemplates (vmapTemplates)

-- hashmap templates

hmapTemplates :: (Monad m, MonadCatch m) => [(Id, Template m)]
hmapTemplates = [
  ("readHMap", t03),
  --("saveHMap", t04),
  ("groupReduceHMap1", t01),
  ("groupReduceHMap2", t02),
  ("countHMap", fromMaybe (error "Maps/HTems: can't find countHVMap template.") $ lookup "countVMap" vmapTemplates),
  ("countHMapMirr", fromMaybe (error "Maps/HTems: can't find countHVMapMirr template.") $ lookup "countVMapMirr" vmapTemplates)
  ]

-- |readHMap template
t03 :: (Monad m, MonadCatch m) => Template m
t03 (Lf (LfTy "DMap" [mode1, kt1, vt1, ordF1, parF1, parD1, mirD1]) :-> 
     Lf (LfTy "DMap" [mode2, kt2, vt2, ordF2, parF2, parD2, mirD2]))
   (LFun _ inN outN)
   | mode1 == nameTy "Hsh" && mode2 == nameTy "Stm" &&
     kt1 == kt2 && vt1 == vt2 = do
     -- check in and out dists are same
     assertM (return $ parD1 == parD2) "par dims don't match"
     assertM (return $ mirD1 == mirD2) "mirror dims don't match"
     -- get input var name 
     getVar (Lf "inMap") inN outVarName
     -- declare loop iterator and end iterator
     (TyV vecmapType) <- getVal inN "vecmapType"
     let iterTy = Lf $ LfTy "ConstIter" [vecmapType] -- TODO !!! pass as shared_ptr, or just as is??? !!!
     newVar (Lf "it") iterTy
     newVar (Lf "end") iterTy
     varExp "itBegin" "inMap" "<v>.begin()" iterTy
     varExp "itEnd" "inMap" "<v>.end()" iterTy
     runGenV "declareVarInit" "decIt" [Lf "it", Lf "itBegin"]
     runGenV "declareVarInit" "decEnd" [Lf "end", Lf "itEnd"]
     -- declare stream var
     varExp "itKey" "it" "<v>->first" kt1
     varExp "itVal" "it" "<v>->second" vt1
     setVar outN "streamVar" $ Tup [Lf "itKey", Lf "itVal"]
     -- if we know the maps size, pass it on
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
t03 t n = terr' t n

-- |groupReduceVMap2 template
-- |local group reduces
t01 :: (Monad m, MonadCatch m) => Template m
t01 (Tup [Tup [kt1, vt1] :-> ity1,
         Tup [kt2, vt2] :-> wt1,
         Tup [wt2, wt3] :-> wt4,
         wt5, 
         (Lf (LfTy "DMap" [mode1, kt3, vt3, of1, pf1, d1, m1]))] :-> 
         (Lf (LfTy "DMap" [mode2, ity2, wt6, of2, pf2, d2, m2])))
   (LFun _ (LTup _ [kfN, vfN, rfN, w0N, inN]) outN) 
   | match kt1 [kt2,kt3] && match vt1 [vt2,vt3] && ity1 == ity2 &&
     match wt1 [wt2,wt3,wt4,wt5,wt6] && 
     mode1 == nameTy "Stm" && mode2 == nameTy "Hsh" = do
     tn <- getTemplateName
     -- sanity check
     -- check in and out dims are the same
     assertM (return $ d1 == d2) "par dims don't match"
     assertM (return $ m1 == m2) "mirror dims don't match"
     -- create new key and new val vars
     newStructVar (Lf "key2") ity1
     runGenV "genTyName" "keyTyName" [Lf "key2"]
     newStructVar (Lf "val2") wt1
     newStructVar (Lf "val3") wt1
     newStructVar (Lf "val4") wt1
     -- create output Map var
     let mapTy = namedTy "LMap" [nameTy "Hsh", ity1, wt1, of2]
     ifnVar "decOutMap" outVarName (Lf "outMap") mapTy
     setVal outN "vecmapType" (TyV mapTy)
     -- create iterator var
     newVar (Lf "it") (Lf $ LfTy "Iter" [mapTy])
     -- get input vars
     getVar (Tup [Lf "key1", Lf "val1"]) inN "streamVar"
     getVar (Lf "w0") w0N outVarName -- (not used)
     -- def "genConsumers" to generate print statements
     setFun outN "genConsumers" nt (\_ -> do
       curNid <- gets genCurrentNode
       genTrace $ "entered " ++ tn ++ ".genConsumers: " ++ (show curNid) ++ "\n"
       -- declare vars
       runGenV "declareVar" "decIt" [Lf "it"]
       runGenV "declareVar" "decKey2" [Lf "key2"]
       runGenV "declareVar" "decVal2" [Lf "val2"]
       runGenV "declareVar" "decVal3" [Lf "val3"]
       runGenV "declareVar" "decVal4" [Lf "val4"]
       k2 <- getLocalVal "key2"
       -- generate code to get new key and new val
       genFunV "genNewKey" kfN (Tup [Lf "key1", Lf "val1"]) n0 (Lf "key2")
       genFunV "genNewVal" vfN (Tup [Lf "key1", Lf "val1"]) w0N (Lf "val2")
       genFunV "combineVals" rfN (Tup [Lf "val2", Lf "val3"]) n0 (Lf "val4")
       -- add init and append statement to consumers
       beginMsg <- temMsg "begin consumer"
       endMsg <- temMsg "end consumer"
       outputDecl outN "<decOutMap>"
       addCode inN "initStream" "// declare <tem> map\n<outMap>.set_empty_key(flocc::<keyTyName>Empty);\n"
       addCode inN "consumers" $ "// begin <tem> consume\n" ++ --beginMsg ++ 
         "<decKey2>\n"++
         "<decVal2>\n"++
         "<decVal3>\n"++
         "<decVal4>\n"++
         "<decIt>\n"++
         "<genNewKey>\n"++
         "<genNewVal>\n"++
         -- there is no way to tell the hashmap what the default value
         -- is (unless we implemented a wrapper than did this)
         (if (wt1 == nullTy) 
         then ("// value type is null\n"++
           "<outMap>[<key2>] = 0;\n") 
         else ("<it> = <outMap>.find(<key2>);\n"++
           "if (<it> == <outMap>.end()) {\n"++ 
           "  <outMap>[<key2>] = <val2>;\n"++
           "} else {\n"++
           "  <val3> = <outMap>[<key2>];\n"++
           "  <combineVals>\n"++
           "  <outMap>[<key2>] = <val4>;\n"++
           "}\n")) ++ 
         "// end <tem> consume\n" -- ++ endMsg
       addCode inN "finStream" ""
       )
t01 t n = terr' t n

-- |groupReduceHMap2 template
-- |local group reduces, exchanges, local group reduces
t02 :: (Monad m, MonadCatch m) => Template m
t02 (Tup [Tup [kt1, vt1] :-> ity1,
         Tup [kt2, vt2] :-> wt1,
         Tup [wt2, wt3] :-> wt4,
         wt5, 
         (Lf (LfTy "DMap" [mode1, kt3, vt3, of1, pf1, d1, m1]))] :-> 
         (Lf (LfTy "DMap" [mode2, ity2, wt6, of2, pf2@(Lf (FunTy parG)), d2, m2])))
   (LFun _ (LTup _ [kfN, vfN, rfN, w0N, inN])    outN) 
   | match kt1 [kt2,kt3] && match vt1 [vt2,vt3] && ity1 == ity2 &&
     match wt1 [wt2,wt3,wt4,wt5,wt6] && 
     mode1 == nameTy "Stm" && mode2 == nameTy "Hsh" = do
     tn <- getTemplateName
     -- sanity check
     -- check in and out dims are the same
     assertM (return $ d1 == d2) "par dims don't match"
     assertM (return $ m1 == m2) "mirror dims don't match"
     -- create new key and new val vars
     newStructVar (Lf "key2") ity1
     runGenV "genTyName" "keyTyName" [Lf "key2"]
     newStructVar (Lf "val2") wt1
     newStructVar (Lf "val3") wt1
     newStructVar (Lf "val4") wt1
     -- create output Map var
     let mapTy = namedTy "LMap" [nameTy "Hsh", ity1, wt1, of2]
     ifnVar "decOutMap" outVarName (Lf "outMap") mapTy
     setVal outN "vecmapType" (TyV mapTy)
     -- create iterator var
     newVar (Lf "it") (Lf $ LfTy "Iter" [mapTy])
     runGenV "declareVar" "decIt" [Lf "it"]
     varExp "itKey" "it" "(<v>->first)" ity1
     varExp "itVal" "it" "(<v>->second)" wt1
     -- get stream var
     getVar (Tup [Lf "key1", Lf "val1"]) inN "streamVar"

     -- vars for redistributing to group by key
     let elTy = Tup [ity1, wt1]
     newStructVar (Lf "el") elTy -- copy of element
     varExp "elK" "el" "<v>.v0" ity1
     runGenV "assignVar" "copyEl" [Lf "el", Tup [Lf "itKey", Lf "itVal"]]      -- pack pair in struc
     runGenV "genTyName" "elTy" [Lf "el"]
     getDimSize "numNodes" d2
     newVar (Lf "rank") intTy -- current partition id
     runGenV "declareVar" "decCons" [Tup [Lf "rank", Lf "el"]]
     varToNodeRankV "getRank" (Lf "elK") "rank" d2 d2 m2      -- work out partition it belongs in
     newVar (Lf "sendCnts") intTy -- sizes in bytes of each send partition
     let vecTy = Lf $ (LfTy "LVec" [elTy])
     newVar (Lf "sendVecs") vecTy -- array of vectors, one for each part
     runGenV "declareArr" "decSendVecs" [Lf "sendVecs", Lf "numNodes"]

     -- create local cart comm
     genSubCartV "localComm" "localRanks" d1 -- use part dim, as alltoallv goes along part dims
     varExp "localCommPtr" "localComm" "&(<v>)" intTy
     -- declare temp vec and alltoall stream
     let vecTy = namedTy "LVec" [elTy]
     newVar (Lf "tmpVec") $ namedTy "SPtr" [vecTy]
     vecTyName <- genTypeName vecTy >>= (return . (fromMaybe (error $ "Templates:" ++ tn ++ " can't get type name of " ++ (show vecTy))))
     varExp "newVec" "" ("new " ++ vecTyName) (Lf $ LfTy "Ptr" [vecTy])
     runGenV "declareVarInit" "decTmpVec" [Lf "tmpVec", Tup [Lf "newVec"]]     
     newVar (Lf "repart") (Lf $ LfTy "Reparter" [Tup [ity1, wt1], vecTy])
     runGenV "declareVarInit" "decRedist" [Lf "repart", Tup [Lf "localCommPtr", Lf "tmpVec"]]

     -- vars for reading partitions into hashmap
     newVar (Lf "recvVec") vecTy
     runGenV "declareVar" "decRecvVec" [Lf "recvVec"]
     newVar (Lf "vit") (Lf $ LfTy "Iter" [vecTy])
     varExp "vitEl" "vit" "(*<v>)" elTy
     runGenV "declareVar" "decVIt" [Lf "vit"]
     runGenV "assignVar" "copyEl2" [Tup [Lf "key2", Lf "val2"], Lf "vitEl"]

     -- def "genConsumers" to generate print statements
     setFun outN "genConsumers" nt (\_ -> do
       curNid <- gets genCurrentNode
       genTrace $ "entered "++tn++".genConsumers: " ++ (show curNid) ++ "\n"
       -- declare vars
       runGenV "declareVar" "decKey2" [Lf "key2"]
       runGenV "declareVar" "decVal2" [Lf "val2"]
       runGenV "declareVar" "decVal3" [Lf "val3"]
       runGenV "declareVar" "decVal4" [Lf "val4"]
       k2 <- getLocalVal "key2"
       -- generate code to get new key and new val
       genFunV "genNewKey" kfN (Tup [Lf "key1", Lf "val1"]) n0 (Lf "key2")
       genFunV "genNewVal" vfN (Tup [Lf "key1", Lf "val1"]) w0N (Lf "val2")
       genFunV "combineVals" rfN (Tup [Lf "val2", Lf "val3"]) n0 (Lf "val4")
       -- debug messages
       beginConMsg <- temMsg "begin consumer"
       endConMsg <- temMsg "end consumer"
       beginFinMsg <- temMsg "begin fin"
       endFinMsg <- temMsg "end fin"
       -- 'create hashmap' declaration
       outputDecl outN "<decOutMap>"
       addCode inN "initStream" $ 
         "// declare hashmap\n"++ -- <decOutMap> // TODO init size\n" ++ 
         "<outMap>.set_empty_key(flocc::<keyTyName>Empty);\n"
       -- create 'populate hashmap' consumer
       addCode inN "consumers" $ "// begin <tem> consume\n" ++
         --beginConMsg++
         "<decKey2>\n"++
         "<decVal2>\n"++
         "<decVal3>\n"++
         "<decVal4>\n"++
         -- TODO try pointers to vals as well as vals
         -- TODO more efficient update (add inline "update" that takes a function)
         "<genNewKey>\n"++
         "<genNewVal>\n"++
         (if (wt1 == nullTy) 
         then ("// value type is null\n"++
           "<outMap>[<key2>] = 0;\n") 
         else ("if (<outMap>.count(<key2>)) {\n"++ 
           "  <val3> = <outMap>[<key2>];\n"++
           "  <combineVals>\n"++
           "  <outMap>[<key2>] = <val4>;\n"++
           "} else {\n"++
           "  <outMap>[<key2>] = <val2>;\n"++
           "}\n")) ++ 
         "// end <tem> consume\n"
         --endConMsg
       -- create 'hashmap distribution' code
       genHasDataPred "hasData" d2 m2
       genSubCartV "localComm" "localRanks" d2
       addCode inN "finStream" $ 
         beginFinMsg ++ 
         "if (<hasData>) {\n"++
         "  // read local hash maps into reparter\n"++
         "  <decTmpVec>\n<decRedist>\n<decIt>\n"++
         "  for (<it> = <outMap>.begin(); <it> != <outMap>.end(); ++<it>) {\n"++
         "    <decCons><copyEl><getRank>\n<repart>.push_back(<rank>, <el>);\n"++
         "  }\n\n"++
         "  // redistribute partition vectors\n"++
         "  <repart>.finish();\n\n"++
         "  // read from recv vectors into local hash map\n"++
         "  <outMap>.clear_no_resize();\n"++
         "  <decVIt>\n"++
         "  <decKey2>\n"++
         "  <decVal2>\n"++
         "  <decVal3>\n"++
         "  <decVal4>\n"++
         "  for (<vit>=<tmpVec>->begin(); <vit>!=<tmpVec>->end(); <vit>++) {\n"++
         "    <copyEl2>\n"++
         -- check if value type is null
         (if (wt1 == nullTy) 
         then ("    // value type is null\n"++
           "    <outMap>[<key2>] = 0;\n") 
         else ("    if (<outMap>.count(<key2>)) {\n"++ 
           "      <val3> = <outMap>[<key2>];\n"++
           "      <combineVals>\n"++
           "      <outMap>[<key2>] = <val4>;\n"++
           "    } else {\n"++
           "      <outMap>[<key2>] = <val2>;\n"++
           "    }\n")) ++
         "  }\n"++
         "}\n"++
         endFinMsg
       {-addCode inN "finStream" $ 
         beginFinMsg ++ 
         "if (<hasData>) {\n"++
         "  // read local hash maps into partition vectors\n"++
         "  <decSendVecs>\n<decIt>\n"++
         "  for (<it> = <outMap>.begin(); <it> != <outMap>.end(); ++<it>) {\n"++
         "    <decCons><copyEl><getRank>\n<sendVecs>[<rank>].push_back(<el>);\n"++
         "  }\n\n"++
         "  // redistribute partition vectors\n"++
         "  <decRecvVec>\n"++
         "  flocc::allToAllVecs<<elTy> >(<sendVecs>, &<recvVec>, &<localComm>);\n\n"++
         "  // read from recv vectors into local hash map\n"++
         "  <outMap>.clear_no_resize();\n"++
         "  <decVIt>\n"++
         "  <decKey2>\n"++
         "  <decVal2>\n"++
         "  <decVal3>\n"++
         "  <decVal4>\n"++
         "  for (<vit>=<recvVec>.begin(); <vit>!=<recvVec>.end(); <vit>++) {\n"++
         "    <copyEl2>\n"++
         "    if (<outMap>.count(<key2>)) {\n"++ 
         "      <val3> = <outMap>[<key2>];\n"++
         "      <combineVals>\n"++
         "      <outMap>[<key2>] = <val4>;\n"++
         "    } else {\n"++
         "      <outMap>[<key2>] = <val2>;\n"++
         "    }\n"++
         "  }\n"++
         "}\n"++
         endFinMsg-}
       )
t02 t n = terr' t n

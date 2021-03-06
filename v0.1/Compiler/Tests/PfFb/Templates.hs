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
module Compiler.Tests.PfFb.Templates where

import Compiler.Back.Graph
import Compiler.Back.GenDecls
import Compiler.Back.Gen
import Compiler.Back.Generators (genTypeName)
import Compiler.Back.Helper
import Compiler.Back.GraphInterpretter
import Compiler.Back.Arrays
import Compiler.Back.CartTopology

--import NodeLayouts
--import FunSynthesis
import Compiler.Back.StrTemplates (StrTem, applyT)

import Control.Monad (foldM)
import Control.Monad.State.Strict (gets, modify)
import Data.Maybe (fromMaybe)
import qualified Data.Set as DS
import qualified Data.IntMap as IM
import qualified Data.Map as DM
import Data.List ((\\), intersperse, zip4, unzip4)
import Data.Char (isAlphaNum)

-- Note: is responsiblity of consumers to check whether
-- there is local data for their part/mirr dims, in initStream
-- and finStream code blocks. i.e. producers will always call 
-- initStream and finStream.

-- Note: all methods that return a vecmap, must set their public
-- vecmapType var to the vecmap type.

{- 
lti 
loadIntPairDStream
dStreamToDVecMap
mapDStream2
eqAllPairsDStreamDVecMap
dVecMapToDStreamLocal
eqJoinDStreamDVecMap
mapDStream2
cardDStream
printInt
-}

-- |nt. shorthand for Nothing.
nt = Nothing

terr :: String -> Ty -> NodeTreeEx -> a
terr tn ty nodes = error $ "Template " ++ tn ++ " error\nType: " ++ (show ty) ++ "\nNodes: " ++ (show nodes) ++ "\n"

terr' :: Monad m => Ty -> NodeTreeEx -> GenM m
terr' ty nodes = do
  tn <- getTemplateName
  terr tn ty nodes

templates :: Monad m => [(Id, Template m)]
templates = [
  ("ifFun", ifT),
  ("lti", t21),
  ("loadIntPairDStream", t22),
  ("mapDStream1", t23),
  ("mapDStream2", t23),
  ("dStreamToDVecMap", t24),
  ("dVecMapToDStreamLocal", t25),
  ("allPairsDVecMap", t26),
  ("eqJoinDStreamDVecMap", t27),
  ("reduceDStream", t28),
  ("addi", t29),
  ("printInt", t30),
  ("sortDVecMap", t31)
  ]

nullFun = Lf $ LfTy "NullFun" [];

nameTy :: String -> Ty
nameTy name = Lf $ LfTy name []

namedTy :: String -> [Ty] -> Ty
namedTy name l = Lf $ LfTy name l

temMsg :: Monad m => String -> GenM1 m Code
temMsg str = do
  -- get current function/template name
  tname <- getTemplateName
  -- display a comment, and a debug statement
  return $ "// " ++ str ++ " " ++ tname ++ "\n" ++
           "#ifdef DEBUG\n" ++
           "std::cerr << thisRank << \") " ++ str ++ " " ++ tname ++ "\\n\";\n"++ 
           "#endif\n"

dbgVal :: Monad m => String -> Code -> GenM1 m Code
dbgVal name val = do
  -- get current function/template name
  tname <- getTemplateName
  -- make template val
  return $ "// DBG " ++ tname ++ "." ++ name ++ "\n" ++
           "#ifdef DEBUG\n" ++
           "std::cerr << thisRank << \") DBG " ++ tname ++ "." ++ name ++ " = \" << " ++ val ++ " << \"\\n\";\n"++ 
           "#endif\n"

outMain :: Monad m => Code -> GenM m
outMain code = do
  bstr <- temMsg "BEGIN"
  estr <- temMsg "END"
  output "main" bstr
  output "main" code
  output "main" estr

-- |genVarExps srcId tem ty params. Generates a new var exp of type ty for each param,
-- |using the template tem, replacing <p> with each param, and replacing 
-- |<v> with the srcId. 
genVarExps :: Monad m => Id -> StrTem -> Ty -> [Code] -> GenM1 m ([IdTree], [IdTree])
genVarExps srcId tem ty params = do
  -- make vars
  varNames <- mapM (\param -> 
    do vid <- newInt ; 
       varExp ("varExp" ++ (show vid)) srcId (applyT tem [("p", param)]) ty ; 
       return $ Lf ("varExp" ++ (show vid))) params
  -- get var ids
  vids <- mapM (\(Lf n) -> do (VarV _ v) <- getLocalVal n; return v) varNames
  -- return
  return (varNames, vids)

-- |ifFun template (for conditionals)
ifT :: Monad m => Template m
ifT (Tup [t1, (t2 :-> t3), (t4 :-> t5)] :-> t6)
    (LFun _ (LTup _ [predN, thenN, elseN]) thisN) 
    | t1 == boolTy && match nullTy [t2,t4] && 
      match t6 [t3,t5] = do
      -- get predicate var
      getVar (Lf "predV") predN outVarName
      -- declare result var
      ifnVar "decOut" outVarName (Lf "res") t3
      -- gen then/else blocks
      newVar (Lf "nullV") nullTy
      genFunV "thenCode" thenN (Lf "nullV") (Lf "res")
      genFunV "elseCode" elseN (Lf "nullV") (Lf "res")
      -- gen if block
      setFun thisN "gen" nt (\_ -> do
       output "main" $ 
         "// <tem>\n<decOut>\n" ++
         "if (<predV>) {\n<thenCode>\n} else {\n<elseCode>\n}\n"
       return ())
ifT t n = terr' t n
 
-- |lti template
t21 :: Monad m => Template m
t21 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c)
   | match intTy [t1,t2] && t3 == boolTy = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     --     decName  publicName localName type
     ifnVar "decOut" outVarName (Lf "cv") t3
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = <av> < <bv>;\n"
       return ())
t21 t n = terr' t n

-- TODO ENSURE GENERATED AS DISTINCT BELOW:
-- |loadIntPairDStream template
t22 :: Monad m => Template m
t22 (t1 :-> (Lf (LfTy "DMap" [mode, keyT, valT, ordF, parF, parD, mirD])))
   (LFun _ inN outN)
   | t1 == nullTy && mode == nameTy "Stm" &&
     keyT == Tup [intTy, intTy] && valT == nullTy = do
     -- declare loop var 
     newVar (Lf "i") intTy
     -- declare stream var
     newVar (Lf "nullV") nullTy
     newVar (Tup [Lf "s1", Lf "s2"]) (Tup [intTy, intTy])
     setVar outN "streamVar" $ Tup [Tup [Lf "s1", Lf "s2"], Lf "nullV"]
     -- when gen is called, generate loop
     setFun outN "gen" nt (\_ -> do
       -- gen consumers
       callAll outN "genConsumers" nt
       getCode "init" outN "initStream"
       getCode "fin" outN "finStream"
       getCode "consume" outN "consumers"
       -- local data pred
       genHasDataPred "hasData" parD mirD
       -- output code
       outMain $
         "<init>\n"++
         "if (<hasData>) {\n" ++
         "int <s1>, <s2>;\n"++
         "for (int <i> = 0; <i> < 1024*1024/Nproc; <i>++) {\n"++
         "  <s1> = rand() % 1024; <s2> = rand() % 1024;\n"++
         "  <consume>\n"++
         "}\n"++
         "}\n"++
         "<fin>\n"
       return ())
t22 t n = terr' t n

-- |mapDStream template
t23 :: Monad m => Template m
t23 (Tup [((Tup [kt1, vt1]) :-> (Tup [kt2, vt2])), 
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
     -- when gen is called, generate loop
     setFun outN "genConsumers" nt (\_ -> do
       -- generate map fun implementation
       genFunV "funCode" funN (Tup [Lf "k1", Lf "v1"]) (Tup [Lf "k2", Lf "v2"])
       -- gen consumers
       callAll outN "genConsumers" nt
       getCode "init" outN "initStream"
       getCode "fin" outN "finStream"
       getCode "consume" outN "consumers"
       -- add these consumers to producer
       addCode inN "consumers" $ "// BEGIN <tem> consume:\n<decStmVar><funCode>\n<consume>\n// END <tem> consume\n"
       addCode inN "initStream" "<init>"
       addCode inN "finStream" "<fin>"
       return ())
t23 t n = terr' t n

-- |dStreamToDVecMap template - does an alltoallv to redistribute using fst
t24 :: Monad m => Template m
t24 (Lf (LfTy "DMap" [mode1, kt1, vt1, ordF1, parF1, parD1, mirD1]) :-> 
     Lf (LfTy "DMap" [mode2, kt2, vt2, ordF2, parF2@(Lf (FunTy parG)), parD2, mirD2]))
   (LFun _ inN outN)
   | kt1 == kt2 && vt1 == vt2 &&
     mode1 == nameTy "Stm" && mode2 == nameTy "Vec" = do
     tn <- getTemplateName
     -- check in and out dims are the same
     assertM (return $ parD1 == parD2) "par dims don't match"
     assertM (return $ mirD1 == mirD2) "mirror dims don't match"
     -- create local cart comm
     genSubCartV "localComm" "localRanks" parD1 -- use part dim, as alltoallv goes along part dims
     varExp "localCommPtr" "localComm" "&(<v>)" intTy
     -- get input stream vars
     getVar (Lf "svar") inN "streamVar"
     -- copy to struct for storage
     newStructVar (Lf "structVar") $ Tup [kt1, vt1]
     runGenV "declareVar" "decStructVar" [Lf "structVar"]
     runGenV "assignVar" "packVar" [Lf "structVar", Lf "svar"] 
     -- declare proj function, for the vecmap
     let (Lf (FunTy ordFun)) = ordF2
     (ordDomTy :-> ordRanTy) <- getGraphTy ordFun
     projFunTy <- genStaticFun ordFun (Just $ Tup [kt2, vt2]) Nothing "inline static"
     -- NOTE: output vec map will be sorted in same way as input, so pass this info to vecmap constructor...
     -- TODO ...
     -- declare vecmap output and alltoall stream
     let outTy = Lf $ LfTy "VecMap" [Tup [kt2, vt2], kt2, ordRanTy, projFunTy]
     setVal outN "vecmapType" (TyV outTy)
     outmapTyName <- genTypeName outTy >>= (return . (fromMaybe (error $ "Templates:" ++ tn ++ " can't get type name of " ++ (show outTy))))
     varExp "newVecmap" "" ("new " ++ outmapTyName) (Lf $ LfTy "Ptr" [outTy])
     ifnVarInit "decOut" outVarName (Lf "outmap") (Lf $ LfTy "SPtr" [outTy]) (Just $ Tup [Lf "newVecmap"])
     newVar (Lf "repart") (Lf $ LfTy "Reparter" [Tup [kt2, vt2], outTy])
     runGenV "declareVarInit" "decRedist" [Lf "repart", Tup [Lf "localCommPtr", Lf "outmap"]]
     -- apply output part function (fst), and hash it to get rank should live on
     (parInTy :-> parOutTy)  <- getGraphTy parG
     newVar (Lf "pval") parOutTy
     runGenV "declareVar" "decPval" [Lf "pval"]
     genTyFunV "appPf" parF2 (Lf "svar") (Lf "pval")
     newVar (Lf "rank") intTy
     runGenV "declareVar" "decRank" [Lf "rank"]
     varToNodeRankV "getRank" (Lf "pval") "rank" parD1 parD1 mirD1
     -- make dbgval msg
     dbgMsg1 <- dbgVal "count" "<repart>.getConsumer()->size()"
     -- when gen is called, generate redist code
     setFun outN "genConsumers" nt (\_ -> do
       -- add consumers to producer
       addCode inN "initStream" $ "// BEGIN <tem> init\n<decStructVar><decOut>" ++ 
                                  -- "<outmap>->setSecondarySorted();\n" ++ -- as stream is sorted already
                                  "<decRedist>\n// END <tem> init\n"
       addCode inN "finStream" $ 
         "// BEGIN <tem> fin\n<repart>.finish();\n"++dbgMsg1++
         "\n// END <tem> fin\n"
       addCode inN "consumers" $ 
         "// BEGIN <tem> consume\n<packVar>\n<decPval>\n"++
         "// App part fun:\n<appPf>\n// App part fun end\n<decRank>\n<getRank>\n"
         ++"<repart>.push_back(<rank>, <structVar>);\n//END <tem> consume\n"
       return ())
t24 t n = terr' t n

-- (TODO POSTPONED make conversion from Int hash to a tuple of Ints using sizes of dimensions (i.e. using Mod and Arrays))
-- ...

-- |dVecMapToDStreamLocal template
t25 :: Monad m => Template m
t25 (Lf (LfTy "DMap" [mode1, kt1, vt1, ordF1, parF1, parD1, mirD1]) :-> 
     Lf (LfTy "DMap" [mode2, kt2, vt2, ordF2, parF2, parD2, mirD2]))
   (LFun _ inN outN)
   | mode1 == nameTy "Vec" && mode2 == nameTy "Stm" &&
     kt1 == kt2 && vt1 == vt2 = do
     -- check in and out dists are same
     -- assertM (return $ parF1 == parF2) $ "ERROR: dVecMapToDStreamLocal: par funs don't match:\n" ++ (show parF1) ++ "\n" ++ (show parF2)
     assertM (return $ parD1 == parD2) "par dims don't match"
     assertM (return $ mirD1 == mirD2) "mirror dims don't match"
     -- get input var name 
     getVar (Lf "inVec") inN outVarName
     -- declare loop iterator and end iterator
     (TyV vecmapType) <- getVal inN "vecmapType"
     let iterTy = Lf $ LfTy "ConstIter" [vecmapType] -- TODO !!! pass as shared_ptr, or just as is??? !!!
     newVar (Lf "it") iterTy
     newVar (Lf "end") iterTy 
     varExp "itBegin" "inVec" "<v>->cbegin()" iterTy
     varExp "itEnd" "inVec" "<v>->cend()" iterTy
     runGenV "declareVarInit" "decIt" [Lf "it", Lf "itBegin"]
     runGenV "declareVarInit" "decEnd" [Lf "end", Lf "itEnd"]
     -- declare stream var
     varExp "itKey" "it" "<v>->v0" kt1
     varExp "itVal" "it" "<v>->v1" vt1
     setVar outN "streamVar" $ Tup [Lf "itKey", Lf "itVal"]
     -- when gen is called, generate loop
     setFun outN "gen" nt (\_ -> do
       -- gen consumers
       callAll outN "genConsumers" nt
       getCode "init" outN "initStream"
       getCode "fin" outN "finStream"
       getCode "consume" outN "consumers"
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
       return ())
t25 t n = terr' t n

-- TODO FIX SO USES NEW VEC MAPS
-- |allPairsDVecMap template
t26 :: Monad m => Template m
t26 (Tup [funTy@(Tup [kt1, vt1] :-> kt),
          Lf (LfTy "DMap" [mode1, kt2, vt2, ordF1, parF1, parD1, mirD1])] :-> 
     Lf (LfTy "DMap" [mode2, Tup [kt3, kt4], Tup [vt3, vt4], ordF2, parF2, parD2, mirD2]))
   (LFun _ (LTup _ [inFunN, inVecN]) outN)
   | mode1 == nameTy "Vec" && mode2 == nameTy "Stm" &&
     match kt1 [kt2,kt3,kt4] && match vt1 [vt2,vt3,vt4] = do
     -- check in and out dists are same
     assertM (return $ parD1 == parD2) "par dims don't match"
     assertM (return $ mirD1 == mirD2) "mirror dims don't match"
     let (Lf (FunTy ordFun)) = ordF1
     ordFunTy <- getGraphTy ordFun
     projFunTy <- genStaticFun ordFun (Just $ Tup [kt2, vt2]) (Just kt) "inline static"
     runGen "genTyName" "searchKT" [TyV kt]
     runGen "genTyName" "searchProjT" [TyV projFunTy]
     assertM (return $ funTy == ordFunTy) $ "proj fun type doesn't match ordering fun type: " ++ (show funTy) ++ " != " ++ (show ordFunTy)
     -- get input var name 
     getVar (Lf "inVec") inVecN outVarName
     -- declare loop iterators and end iterator
     (TyV vecmapType) <- getVal inVecN "vecmapType"
     let iterTy = Lf $ LfTy "ConstIter" [vecmapType] -- TODO !!! pass as shared_ptr, or just as is??? !!!
     newVar (Tup [Lf "it1", Lf "it2", Lf "eor", Lf "end"]) (Tup [iterTy, iterTy, iterTy, iterTy])
     varExp "itBegin" "inVec" "<v>->cbegin()" iterTy
     varExp "itEnd" "inVec" "<v>->cend()" iterTy
     runGenV "declareVarInit" "decIt1" [Lf "it1", Lf "itBegin"]
     runGenV "declareVarInit" "decIt2" [Lf "it2", Lf "itBegin"]
     runGenV "declareVarInit" "decEor" [Lf "eor", Lf "itBegin"]
     runGenV "declareVarInit" "decEnd" [Lf "end", Lf "itEnd"]
     -- declare stream vars
     varExp "itKey1" "it1" "<v>->v0" kt1
     varExp "itVal1" "it1" "<v>->v1" vt1
     varExp "itKey2" "it2" "<v>->v0" kt1
     varExp "itVal2" "it2" "<v>->v1" vt1
     setVar outN "streamVar" $ Tup [Tup [Lf "itKey1", Lf "itKey2"], Tup [Lf "itVal1", Lf "itVal2"]]
     -- declare compare key values
     newVar (Tup [Lf "key1", Lf "key2"]) (Tup [kt, kt])
     runGenV "declareVar" "decKeys" [Tup [Lf "key1", Lf "key2"]]
     -- generate key proj functions (return type structs)
     genFunV "projKey1" inFunN (Tup [Lf "itKey1", Lf "itVal1"]) (Lf "key1")
     genFunV "projKey2" inFunN (Tup [Lf "itKey2", Lf "itVal2"]) (Lf "key2")
     -- when gen is called, generate loop
     setFun outN "gen" nt (\_ -> do
       -- gen consumers
       callAll outN "genConsumers" nt
       getCode "init" outN "initStream"
       getCode "fin" outN "finStream"
       getCode "consume" outN "consumers"
       -- local data pred
       genHasDataPred "hasData" parD1 mirD1
       -- output code
       outMain $ 
         "<init>\n"++
         "if (<hasData>) {\n"++
         "<decIt1><decIt2><decEor><decEnd><decKeys>\n"++
         "while (<it1> != <end>) {\n"++
         "  <projKey1> // " ++ (show kt) ++ "\n"++
         "  <eor> = <inVec>->findSecEnd<<searchKT>, <searchProjT> >(<it1>, <key1>);\n"++
         "  while (<it1> != <eor>) {\n"++
         "    <it2> = <it1>; <it2>++;\n"++
         "    while (<it2> != <eor>) {\n"++
         "      <consume>\n"++
         "      <it2>++;\n"++
         "    }\n"++
         "    <it1>++;\n"++
         "  }\n"++
         "}}\n"
       {-outMain $ 
         "<init>\n"++
         "if (<hasData>) {\n"++
         "<decIt1><decIt2><decEnd><decKeys>\n"++
         "while (<it1> != <end>) {\n"++
         "  <it2> = <it1>; <it2>++; \n"++
         "  <projKey1><projKey2>\n"++
         "  while (<it2> != <end> && !(<key1> == <key2>)) {\n"++
         "    <consume>\n"++
         "    <it2>++;\n"++
         "    <projKey2>\n"++
         "  }\n"++
         "  <it1>++;\n"++
         "}\n"++
         "}\n"++
         "<fin>\n"-}
       return ())
t26 t n = terr' t n

-- |eqJoinDStreamDVecMap template
t27 :: Monad m => Template m
t27 (Tup [Tup [kt11, vt11] :-> kt1, Tup [kt21, vt21] :-> kt2,
          Lf (LfTy "DMap" [mode1, kt12, vt12, ordF1, parF1, parD1, mirD1]),
          Lf (LfTy "DMap" [mode2, kt22, vt22, ordF2, parF2, parD2, mirD2])] :-> 
     Lf (LfTy "DMap" [mode3, Tup [kt13, kt23], Tup [vt13, vt23], ordF3, parF3, parD3, mirD3]))
   (LFun _ (LTup _ [funN1, funN2, inN1, inN2]) outN)
   | mode1 == nameTy "Stm" && mode2 == nameTy "Vec" && mode3 == nameTy "Stm" &&
     match kt11 [kt12,kt13] && match vt11 [vt12,vt13] &&
     match kt21 [kt22,kt23] && match vt21 [vt22,vt23] = do
     -- check in and out dists are same
     --assertM (return $ parD1 == parD2) "allPairsDVecMap: par dims don't match"
     --assertM (return $ mirD1 == mirD2) "allPairsDVecMap: mirror dims don't match"
     -- get input var names 
     getVar (Tup [Lf "itKey1", Lf "itVal1"]) inN1 "streamVar"
     getVar (Lf "inVec2") inN2 outVarName
     -- declare loop iterators and end iterator
     (TyV vecmap2Type) <- getVal inN2 "vecmapType"
     let iterTy = Lf $ LfTy "ConstIter" [vecmap2Type] -- TODO !!! pass as shared_ptr, or just as is??? !!!
     newVar (Tup [Lf "it2", Lf "end2"]) (Tup [iterTy, iterTy])
     varExp "itEnd2" "inVec2" "<v>->cend()" iterTy
     runGenV "declareVar" "decIt2" [Lf "it2"]
     runGenV "declareVarInit" "decEnd2" [Lf "end2", Lf "itEnd2"]
     -- declare stream vars
     varExp "itKey2" "it2" "<v>->v0" kt21
     varExp "itVal2" "it2" "<v>->v1" vt21
     setVar outN "streamVar" $ Tup [Tup [Lf "itKey1", Lf "itKey2"], Tup [Lf "itVal1", Lf "itVal2"]]
     -- declare compare key values
     newStructVar (Lf "key1") kt1
     newStructVar (Lf "key2") kt1
     runGenV "declareVar" "decKeys" [Tup [Lf "key1", Lf "key2"]]
     -- generate proj function for doing secondary key search
     (GraphV projFun2) <- getFun funN2
     projFun2Ty <- genStaticFun projFun2 (Just $ Tup [kt21, vt21]) (Just kt2) "inline static"
     runGen "genTyName" "searchKT" [TyV kt2]
     runGen "genTyName" "searchProjT" [TyV projFun2Ty]
     -- generate key proj functions (return type structs)
     genFunV "projKey1" funN1 (Tup [Lf "itKey1", Lf "itVal1"]) (Lf "key1")
     genFunV "projKey2" funN2 (Tup [Lf "itKey2", Lf "itVal2"]) (Lf "key2")
     runGenV "assignVar" "copyKey1" [Lf "key2", Lf "key1"] 
     -- when gen is called, generate loop
     setFun outN "genConsumers" nt (\_ -> do
       -- gen consumers
       callAll outN "genConsumers" nt
       getCode "init" outN "initStream"
       getCode "fin" outN "finStream"
       getCode "consume" outN "consumers"
       -- add consumers to producer
       addCode inN1 "initStream" "// BEGIN <tem> init\n<init><decIt2><decEnd2><decKeys>\n// END <tem> init\n"
       addCode inN1 "finStream" "<fin>"
       addCode inN1 "consumers" $
         "// BEGIN <tem> consume\n"++
         "<projKey1> // get key of input stream\n"++
         "<copyKey1> // copy key1 to key2 so loop pred will match on first iteration\n"++
         "<it2> = <inVec2>->findSecBegin<<searchKT>, <searchProjT> >(<key1>); // find first matching value in vecmap\n"++
         "while (<it2> != <end2> && <key1> == <key2>) { // loop while keys match\n"++
         "  <consume>\n"++
         "  <it2>++;\n"++
         "  <projKey2>\n"++
         "}\n"++
         "// END <tem> consume\n"
       return ())
t27 t n = terr' t n

-- |reduceDStream template -- TODO what if empty stream?
t28 :: Monad m => Template m
t28 (Tup [Tup [kt1, vt1] :-> st1, Tup [st2, st3] :-> st4,
          Lf (LfTy "DMap" [mode1, kt2, vt2, ordF1, parF1, parD1, mirD1])] :-> st5)
   (LFun _ (LTup _ [funN1, funN2, inN]) outN)
   | kt1 == kt2 && vt1 == vt2 && match st1 [st2, st3, st4, st5] &&
     mode1 == nameTy "Stm" = do
     -- get input stream vars
     getVar (Tup [Lf "key", Lf "val"]) inN "streamVar"
     -- declare output var
     ifnVar "decOut" outVarName (Lf "st1") st1
     newVar (Lf "fstVal") boolTy
     -- declare temp vars
     newVar (Tup [Lf "st2", Lf "acc"]) $ Tup [st1, st1]
     runGenV "declareVar" "decVars" [Tup [Lf "st2", Lf "acc"]]
     -- apply functions 
     genFunV "appProj" funN1 (Tup [Lf "key", Lf "val"]) (Lf "st1")
     genFunV "appProjInit" funN1 (Tup [Lf "key", Lf "val"]) (Lf "acc")
     genFunV "appCombine1" funN2 (Tup [Lf "st1", Lf "acc"]) (Lf "st2")
     runGenV "assignVar" "appCopy" [Lf "acc", Lf "st2"] 
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
       addCode inN "initStream" $ 
         "// BEGIN <tem> init\n<decOut><decVars>\n"++
         "bool <fstVal> = true;\n"++
         "// END <tem> init\n"
       addCode inN "consumers" $ 
         "// BEGIN <tem> consume\n"++
         "if (<fstVal>) {\n"++
         "  <appProjInit>\n"++
         "  <fstVal> = false;\n"++
         "} else {\n"++
         "  <appProj><appCombine1><appCopy>\n"++
         "}\n"++
         "// END <tem> consume\n"
       addCode inN "finStream" $ 
         -- reduce among nodes that have data
         "// BEGIN <tem> fin\n"++
         "if (<hasData>) {\n"++
         "  <localComm>.Allreduce(&<acc>, &<st1>, sizeof(<resTyName>), MPI_PACKED, <redOp>);\n"++
         "}\n"++
         -- if local comm isn't the global one, broadcast to any remaining ones 
         "if (<localComm> != cartComm) {\n"++
         "  cartComm.Bcast(&<st1>, sizeof(<resTyName>), MPI_PACKED, rootRank);\n" ++
         "}\n"++
         "// END <tem> fin\n"
       return ())
t28 t n = terr' t n

-- |addi template
t29 :: Monad m => Template m
t29 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c)
   | match intTy [t1,t2,t3] = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     --     decName  publicName localName type
     ifnVar "decOut" outVarName (Lf "cv") t3
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = <av> + <bv>;\n"
       return ())
t29 t n = terr' t n

-- |printInt template
t30 :: Monad m => Template m
t30 (t1 :-> t2)
   (LFun _ inN outN)
   | t1 == intTy && t2 == nullTy = do
     -- get input vars
     getVar (Lf "val") inN outVarName
     -- when gen is called, generate print
     setFun outN "gen" nt (\_ -> do
       outMain "if (thisRank == rootRank) std::cout << <val>;\n"
       return ())
t30 t n = terr' t n

-- |sortDVecMap template
t31 :: Monad m => Template m
t31 (Lf (LfTy "DMap" [mode1, kt1, vt1, ordF1, parF1, parD1, mirD1]) :-> 
     Lf (LfTy "DMap" [mode2, kt2, vt2, ordF2, parF2, parD2, mirD2]))
   (LFun _ inN outN)
   | mode1 == nameTy "Vec" && mode2 == nameTy "Vec" &&
     kt1 == kt2 && vt1 == vt2 = do
     -- check in and out dists are same
     assertM (return $ parD1 == parD2) "par dims don't match"
     assertM (return $ mirD1 == mirD2) "mirror dims don't match"
     -- generate proj function class for ordF2
     let (Lf (FunTy ordFun)) = ordF2
     (ordDomTy :-> ordRanTy) <- getGraphTy ordFun
     projFunTy <- genStaticFun ordFun (Just $ Tup [kt2, vt2]) Nothing "inline static"
     -- get input and output var names 
     getVar (Lf "inVec") inN outVarName
     let outTy = Lf $ LfTy "VecMap" [Tup [kt1, vt1], kt1, ordRanTy, projFunTy] -- TODO change second kt1 to return type of orodF1
     setVal outN "vecmapType" (TyV outTy)
     tn <- getTemplateName
     outmapTyName <- genTypeName outTy >>= (return . (fromMaybe (error $ "Templates:" ++ tn ++ " can't get type name of " ++ (show outTy))))
     varExp "newVecmap" "" ("new " ++ outmapTyName) (Lf $ LfTy "Ptr" [outTy])
     ifnVarInit "decOut" outVarName (Lf "outVec") (Lf $ LfTy "SPtr" [outTy]) (Just $ Tup [Lf "newVecmap"])
     -- pass along vector type to consumers
     setVal outN "vecmapType" (TyV outTy)
     -- make dbgval msgs
     dbgMsg1 <- dbgVal "beforeCount" "<inVec>->size()"
     dbgMsg2 <- dbgVal "afterCount" "<outVec>->size()"
     -- when gen is called, generate loop
     setFun outN "gen" nt (\_ -> do
       -- local data pred
       genHasDataPred "hasData" parD1 mirD1
       -- output code
       outMain $
         "<decOut>\n // sort sec key type: "++ (show ordRanTy) ++ "\n"++
         "if (<hasData>) {\n"++
         dbgMsg1 ++ "\n" ++ 
         "<outVec>->assign(<inVec>);"++
         dbgMsg2 ++ "\n" ++
         "}\n"
       return ())
t31 t n = terr' t n

-- |addf template
t16 :: Monad m => Template m
t16 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c)
   | match floatTy [t1,t2,t3] = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     --     decName  publicName localName type
     ifnVar "decOut" outVarName (Lf "cv") t3
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = <av> + <bv>;\n"
       return ())
t16 t n = terr "addf" t n

-- |mulf template
t18 :: Monad m => Template m
t18 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c) 
   | match floatTy [t1,t2,t3] = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "cv") t3
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = <av> * <bv>;\n"
       return ())
t18 t n = terr "mulf" t n

-- |genDMat template
-- |TODO being updated...
t1 :: Monad m => Template m
t1 (inTy :->   
    outT@(Lf (LfTy "DArr" [mode, Tup [t1, t2], t3, layF, parF, dim, mirr]))) 
   (LFun _ numInts distArr) 
   | mode == (nameTy "Arr") && match intTy [inTy,t1,t2] && t3 == floatTy = do -- TODO check parF is FNull, and dim is empty tup
     -- TODO make work with different layout and mirror dims
     
     -- make index space for array
     getVar (Lf "nv") numInts outVarName
     (VarV _ (Lf nvid)) <- getLocalVal "nv"
     let space = createSpaceFromLens ["0","0"] [nvid,nvid] ["1","1"]
     
     -- declare and init array
     -- (its a random square array so both layouts are equivalent!)
     -- make iterator for whole array
     -- make loops for iterator
     -- add line that inits an element to a random float
     -- generate...

     -- get var for current nodeset (lookup using dist type)
     --getNodeSetVar "ns" nodeSet -- TODO replace with getTopology
     --varExp "numNodes" "ns" "<v>.partitionCount" intTy
     --varExp "nodeIdx" "ns" "<v>.partitionRank" intTy
     -- create intermediate vars
     --newVar (Lf "startI") intTy
     --newVar (Lf "localN") intTy
     --newStructVar (Lf "s") (Tup [intTy, intTy])
     --aliasVar (Tup [Lf "i", Lf "v"]) (Lf "s")
     -- get input var 
     getVar (Lf "n") numInts outVarName
     -- create array bounds vars
     newVar (Lf "lens") (listTy uintTy)
     newVar (Lf "starts") (listTy intTy)
     nvar <- getLocalVal "n"
     runGen "litArr" "decLens"   [IdV "lens", ListV [nvar, nvar]]
     runGen "litArr" "decStarts" [IdV "starts", ListV $ map (LitV . UIntVal) [0, 0]]
     -- create output var if doesn't already exist
     varExp "mpiFloat" "" "MPI::DOUBLE" nullTy
     ifnVarInit "decArr" outVarName (Lf "arr") outT (Just $ Tup [Lf "mpiFloat", Lf "lens", Lf "starts"])
     -- create iterator var
     newVar (Lf "it") (idxIterTy outT)
     newVar (Lf "endIt") (idxIterTy outT)
     varExp "getBeginIt" "arr" "<v>.beginIndex()" (idxIterTy outT)
     varExp "getEndIt" "arr" "<v>.endIndex()" (idxIterTy outT)
     runGenV "declareVarInit" "decIt" [Tup [Lf "it", Lf "endIt"], Tup [Lf "getBeginIt", Lf "getEndIt"]]
     -- make bounds accessible to consumer templates
     (startns,_) <- genVarExps "" "<p>" intTy $ map show [0,0]
     (endNames,_) <- genVarExps "" "<p>" intTy $ map show [0,0]
     --(endNames,_) <- genVarExps "" "<p>-1" intTy $ map show [nvar,nvar]
     (lenNames,_) <- genVarExps "" "<p>" inTy $ map show [nvar,nvar]
     setVar distArr "arrayStarts" $ Tup startns
     setVar distArr "arrayEnds" $ Tup endNames
     setVar distArr "arrayLens" $ Tup lenNames
     -- when gen is called, generate assignment
     setFun distArr "gen" nt (\_ -> do
       output "main" $
         "// genSqMatrix: \n"++
         -- dec array bounds
         "<decLens>\n<decStarts>\n"++
         -- declare array
         "<decArr>\n"++
         -- init array elements
         "if (top->isOnRoot()) {\n"++
         "  <decIt>\n"++
         "  for (; <it> != <endIt>; <it>++) {\n"++
         "    *(<it>.getElement()) = 2.0;\n"++
         "  }\n"++
         "}\n"
       return ())
t1 t n = terr "genSqMatrix" t n

-- genSqMatrix:
-- ---------------
-- generate MPI type for matrix elements (here always floats/doubles)
-- declare empty array
-- if we are on the fringe of all dims
	-- create bounds from n, using layout func to translate to right indices
	-- declare a root array, with using those bounds
	-- iterate over root array
		-- for each element, use invLayotF to translate to original index
		-- use that index to make the value for this element
		-- set the value of that element to the computed value

type TopDimSpec = Int
topDimMirr = -2
topDimFringe = -1;
topDimPart arrDim = arrDim

isDimMirr = (topDimMirr==)
isDimFringe = (topDimFringe==)
isDimPart d = (d >= 0) && (d <= 1000)
getPartArrDim d = d

dimDistToInt :: Ty -> Int
dimDistToInt (Lf (LfTy name [])) = case name of
  ('P':'a':'r':'t':numStr) -> topDimPart $ ((read numStr) :: Int)
  "Fringe" -> topDimFringe
  "Mirr" -> topDimMirr

-- |dimDistsToInts numTopDims partType. Returns the array that says
-- |how to distribute this array on the cartesian toplology. 
dimDistsToInts :: Int -> Ty -> [Int]
dimDistsToInts numTopDims (Lf (LfTy "DimDists" l)) = case l of
  _ | length l == numTopDims -> map dimDistToInt l
  _                          -> error $ "dimDistsToInts: part type " ++ (show l) ++ " must have " ++ (show numTopDims) ++ " elements."
dimDistsToInts numTopDims (Lf (LfTy "NullDim" [])) = map (\_ -> topDimFringe) [0..(numTopDims-1)]
dimDistsToInts _ val = error $ "dimDistsToInts:" ++ (show val)

replaceDistArrDims :: [Int] -> [Int] -> [Int]
replaceDistArrDims subs dims = map (\d -> if isDimPart d then subs !! (getPartArrDim d) else d) dims

countFringeToPart :: [Int] -> [Int] -> Int
countFringeToPart from to = length $ filter (\(f,t) -> f == (-1) && t >= 0) $ zip from to

-- |scatterArr template
t2 :: Monad m => Template m
t2 (inTy@(Lf (LfTy "DistArr" [t1, t2, inLay,  inLay1,  inPart,  inDims,  Lf (LfTy "MirrDims" inMirrs )])) :-> 
    outT@(Lf (LfTy "DistArr" [t3, t4, outLay, outLay1, outPart, outDims, Lf (LfTy "MirrDims" outMirrs)]))) 
   (LFun _ inArr outArr) 
   | t1 == t3 && t2 == t4 && inLay == outLay && (DS.fromList inMirrs) == (DS.fromList outMirrs) = do
    -- get input var name
    getVar (Lf "in") inArr outVarName
    -- get/create output var
    varExp "mpiElTy" "in" "<v>.getElementType()" nullTy
    ifnVarInit "decOut" outVarName (Lf "out") outT (Just $ Lf "mpiElTy")
    -- for now examine inDims and outDims to get partitioning information
    -- TODO reimplement so it analyses partition function, layout function, dims, and mirr list
    newVar (Lf "bf") (listTy intTy)
    newVar (Lf "af") (listTy intTy)
    numTopDims <- gets (globNumTopDims.genConsts)
    let beforeInts = dimDistsToInts numTopDims inDims
    let afterInts = dimDistsToInts numTopDims outDims
    -- (apply layout function to int lists)
    -- translate virtual array dims to physical ones
    let numIndices = length $ flattenTree t1
    let virtIndices = [0..(numIndices-1)]
    let physIndices = appLayout inLay virtIndices
    let beforeInts' = replaceDistArrDims physIndices beforeInts
    let afterInts' = replaceDistArrDims physIndices afterInts
    --error $ "scatterArr: " ++ (show beforeInts) ++ " -> " ++ (show afterInts) ++ "\n" ++ (show beforeInts') ++ " -> " ++ (show afterInts')
    runGen "litArr" "decBf" [IdV "bf", ListV $ map (LitV . IntVal) beforeInts']
    runGen "litArr" "decAf" [IdV "af", ListV $ map (LitV . IntVal) afterInts']
    -- get parameter types for scatter call 
    mbVTn <- genTypeName t2
    let vTn = fromMaybe (error $ "ArrTemplates:scatterArr: cant gen name for array element type " ++ (show t2) ++ "!\n") mbVTn
    varExp "V" "" vTn nullTy
    varExp "NArr" "" (show $ length $ flattenTree t1) uintTy
    varExp "NPart" "" (show $ countFringeToPart beforeInts' afterInts') uintTy
    -- create generate function
    setFun outArr "gen" nt (\_ -> do
      output "main" $
        "// scatterArr: \n"++
        -- dec before and after dist flags
        "<decBf>\n<decAf>\n"++
        -- declare result array
        "<decOut>\n"++
        -- do scatter
        "  top->scatterArrayBlocked<<V>, <NArr>, <NPart>>(&<in>, &<out>, <bf>, <af>);\n"
      return ())
t2 t n = terr "scatterArr" t n

-- |mirrorArr template
t3 :: Monad m => Template m
t3 (inTy@(Lf (LfTy "DistArr" [t1, t2, inLay,  inLay1,  inPart,  inDims,  Lf (LfTy "MirrDims" inMirrs )])) :-> 
    outT@(Lf (LfTy "DistArr" [t3, t4, outLay, outLay1, outPart, outDims, Lf (LfTy "MirrDims" outMirrs)]))) 
   (LFun _ inArr outArr) 
   | t1 == t3 && t2 == t4 && inLay == outLay && inPart == outPart = do
    -- get input var name
    getVar (Lf "in") inArr outVarName
    -- get/create output var
    varExp "mpiElTy" "in" "<v>.getElementType()" nullTy
    ifnVarInit "decOut" outVarName (Lf "out") outT (Just $ Lf "mpiElTy")
    -- for now examine inDims and outDims to get mirroring information
    -- TODO reimplement so it analyses the MirrDims arrays
    newVar (Lf "bf") (listTy intTy)
    newVar (Lf "af") (listTy intTy)
    numTopDims <- gets (globNumTopDims.genConsts)
    let beforeInts = dimDistsToInts numTopDims inDims
    let afterInts = dimDistsToInts numTopDims outDims
    -- (apply layout function to int lists)
    -- translate virtual array dims to physical ones
    let numIndices = length $ flattenTree t1
    let virtIndices = [0..(numIndices-1)]
    let physIndices = appLayout inLay virtIndices
    let beforeInts' = replaceDistArrDims physIndices beforeInts
    let afterInts' = replaceDistArrDims physIndices afterInts
    --error $ "mirrorArr: " ++ (show beforeInts) ++ " -> " ++ (show afterInts) ++ "\n" ++ (show beforeInts') ++ " -> " ++ (show afterInts')
    runGen "litArr" "decBf" [IdV "bf", ListV $ map (LitV . IntVal) beforeInts']
    runGen "litArr" "decAf" [IdV "af", ListV $ map (LitV . IntVal) afterInts']
    -- get parameter types for mirror
    mbVTn <- genTypeName t2
    let vTn = fromMaybe (error $ "ArrTemplates:scatterArr: cant gen name for array element type " ++ (show t2) ++ "!\n") mbVTn
    varExp "V" "" vTn nullTy
    varExp "NArr" "" (show $ length $ flattenTree t1) uintTy
    -- NEW: use static buffer to receive into
    newVar (Lf "buffer") (Lf $ LfTy "Ptr" [t2])
    (VarV _ (Lf bufVid)) <- getLocalVal "buffer"
    mbElTn <- genTypeName t2
    let vTn = fromMaybe (error $ "ArrTemplates:mirrorArr: cant gen name for array element type " ++ (show t2) ++ "!\n") mbElTn
    let decBuffer = "static " ++ vTn ++ " " ++ bufVid ++ "[5000*5000*2];\n"; -- TODO change to get max sizes from input
    -- create generate function
    setFun outArr "gen" nt (\_ -> do
      output "main" $
        "// mirrorArr: \n"++
        -- dec before and after dist flags
        "<decBf>\n<decAf>\n"++
        -- declare result array
        "<decOut>\n"++ decBuffer ++ "\n" ++ 
        -- do scatter
        "  top->mirrorArray<<V>, <NArr>>(&<in>, &<out>, <bf>, <af>, <buffer>);\n"
      return ())
t3 t n = terr "mirrorArr" t n

getLitInt :: Node -> Int
getLitInt n = case nodeTy n of
  LitNd (IntVal v) -> v
  other -> error $ "getLitInt: expected literal node with int value, but passed: " ++ (show n)

getLitIntList :: Monad m => NodeTreeEx -> GenM1 m [Int]
getLitIntList nodeTree = do
  let nid = fst $ treeLabel nodeTree
  -- get graphs
  graphs <- gets genGraphs
  -- get list node
  let [lstNode] = getNodes "ArrTemplates:getLitIntList:" graphs [nid]
  -- get lit nodes
  let idList = nodeIn lstNode
  let litNodes = getNodes "ArrTemplates:getLitIntList:" graphs idList
  let vals = map getLitInt litNodes
  return vals
--getLitIntList other = error $ "getLitIntList: bad argument: " ++ (show other)

nestCode :: [(Code, Code)] -> Code
nestCode ((begin,end):rest) = begin ++ (nestCode rest) ++ end
nestCode [] = ""

escapeStr :: String -> String
escapeStr s = map (\c -> if isAlphaNum c then c else '_') s

genArrIdxLoop :: Monad m => StrTem -> StrTem -> StrTem -> Id -> Id -> [(String, String)] -> GenM1 m (Code, (Code, Code))
genArrIdxLoop begin startPat endPat idxVn itVn patVals1 = do
  -- pattern values
  (VarV _ (Lf itVid)) <- getLocalVal itVn
  (VarV _ (Lf idxVid)) <- getLocalVal idxVn
  let patVals = patVals1 ++ [("idx", idxVid), ("it", itVid), ("eit", escapeStr itVid)]
  -- use vals in templates
  let start = applyT startPat patVals
  let end = applyT endPat patVals
  let params = (patVals ++ [("start", start), ("end", end)])
  let declPat =  "const int <eit>Start = <start>;\n"++
                 "const int <eit>End = <end>;\n"++
                 "const unsigned int <eit>Len = <eit>End-<eit>Start+1;\n"
  let decl = applyT declPat params 
  let beginPat = "for (int <idx> = 0; <idx> < <eit>Len; <idx>++) {\n" ++
                 "  <it> = <eit>Start+<idx>;\n" ++ begin
  let begin = applyT beginPat params
  return (decl, (begin, "}\n"))

getArrBounds :: Monad m => NodeTreeEx -> Id -> Id -> Id -> Ty -> [Int] -> GenM1 m ([IdTree], [IdTree])
getArrBounds arrNode boundId arrName methName ty indices = do
  -- get bounds either from templates, or using getDimX functions
  mbVal <- getValMaybe arrNode boundId
  case mbVal of
    -- get starts from arr2 template
    Just (VarV _ (Tup vids)) -> do
      (names,_) <- genVarExps "" "<p>" intTy $ map (treeLeaf $ "getArrBounds: " ++ (show arrNode) ++ " " ++ boundId) vids
      return (names, vids) 
    -- gen starts at runtime from arr2 
    Nothing -> do
      pr <- genVarExps arrName ("<v>." ++ methName ++ "(<p>)") ty $ map show indices
      return pr

genArrLoops :: Monad m => Id -> [IdTree] -> [IdTree] -> [IdTree] -> [IdTree] -> [IdTree] -> [Int] -> GenM1 m [(Code, (Code, Code))]
genArrLoops arrVid startVids endVids startns idxNames itns indices = do
  loops <- mapM (\dim -> let (Lf st, Lf end) = (startVids !! dim, endVids !! dim) in
     if st == end -- check if start and end are same, in which case just assign in2It to start
     then do n <- newInt ;
             runGenV "assignVar" ("ass"++(show n)) [itns !! dim, startns !! dim] ; 
             return ("", ("<ass"++(show n)++">", "")) 
     else genArrIdxLoop "" "<st>" "<end>" 
                        (treeLeaf ("genArrLoops1: "++(show (arrVid, dim))) $ idxNames !! dim)
                        (treeLeaf ("genArrLoops2: "++(show (arrVid, dim))) $ itns !! dim) 
                        [("arr", arrVid), ("dim", show dim), ("st", st), ("end", end)]) indices
  return loops

brak :: String -> String
brak s = "<" ++ s ++ ">"

concatProj :: (a -> String) -> [[a]] -> String
concatProj pf l = concat $ map (concat.(map pf)) l

genScalVar :: Monad m => Ty -> StrTem -> [(Id, String)] -> GenM1 m (Id, Code) 
genScalVar ty tem env = do
  -- create id for var and varexp
  num <- newInt
  let varName = "v" ++ (show num)
  let valName = "c" ++ (show num)
  -- create val exp
  let val = applyT tem env
  varExp valName "" val ty
  -- declare var, and assign value to it   
  let decName = "dec" ++ varName;  
  newVar (Lf varName) ty
  runGenV "declareVarInit" decName [Lf varName, Lf valName]
  return (varName, brak decName) 

genArrLoop :: Monad m => [(Id, Id, Id, Id)] -> GenM1 m (Code, Code)
genArrLoop vars = do
  let (idxVars, startVars, endVars, stepVars) = unzip4 vars
  -- make inits
  let initL = map (\(i,s) -> (brak i) ++ " = " ++ (brak s)) $ zip idxVars startVars
  let inits = concat $ intersperse ", " initL
  -- make pred
  let pred = (brak $ head idxVars) ++ " < " ++ (brak $ head endVars)
  -- make incs
  let incL = map (\(i,s) -> (brak i) ++ " += " ++ (brak s)) $ zip idxVars stepVars
  let incs = concat $ intersperse ", " incL
  -- apply template and return loop
  let tem = "for (<inits>; <pred>; <incs>) {\n"
  let code = applyT tem [("inits", inits), ("pred", pred), ("incs", incs)]
  return (code, "}\n")

genPrintInt :: Id -> Code
genPrintInt v = "printf(\"%f\", " ++ (brak v) ++ ");\n";

genDebugLoop :: Monad m => String -> String -> [(Id, Id, Id, Id)] -> GenM1 m (Code, Code)
genDebugLoop n dim vars = do
  let (idxVars, startVars, endVars, stepVars) = unzip4 vars
  let prints = map (\(i,s,e,sp) -> "printf(\"%i: " ++ (brak i) ++ " %s(%s) = %i in [%i..%i:%i]\\n\", top->getRank(), \""++n++"\", \"" ++ dim ++ "\", " 
                     ++ (brak i) ++ ", " ++ (brak s) ++ ", " ++ (brak e) ++ ", " ++ (brak sp) ++ ");\n") vars
  prints' <- mapM expandTem prints
  return $ ("#ifdef DEBUG\n" ++ (concat prints')++("printf(\"\\n\");\n" ++ "\n#endif\n"), "")

{-genArrAcc :: Monad m => Ty -> Id -> [(Id, Id)] -> GenM1 m Id
genArrAcc ty arrV vars = do
  -- make array idx
  let (idxVars, lenVars) = unzip $ map (\(i,v) -> (brak i, brak v)) vars
  --let coeffs = lenVars ++ ["1"]
  --let hdIdx = head idxVars
  --let idx = foldl (\acc -> \(c,i) -> i ++ "+(" ++ c ++ "*(" ++ acc ++ "))") hdIdx (zip coeffs idxVars)
  let idx = concat $ intersperse " + " idxVars
  -- return array element
  num <- newInt
  let n = "el"++(show num)
  varExp n (brak arrV) ("<v>[" ++ idx ++ "]") ty
  return n-}

alternate :: [a] -> [a] -> [a]
alternate l1 l2 = case (l1,l2) of
  (h1:t1, h2:t2) -> h1:h2:(alternate t1 t2)
  ([], _) -> []
  (_, []) -> []

{-
          if (v551[0] < v550.getDimStart(0) || v551[0] > v550.getDimEnd(0)) {
            printf("dim0 %i out of bounds [%i,%i]\n", v551[0], v550.getDimStart(0), v550.getDimEnd(0));
            throw 1;
          }
          if (v551[1] < v550.getDimStart(1) || v551[1] > v550.getDimEnd(1)) {
            printf("dim1 %i out of bounds [%i,%i]\n", v551[1], v550.getDimStart(1), v550.getDimEnd(1));
            throw 1;
          }
          
-}

-- arr0, buf0St, buf0Len, idx0St, idx0Len
--createArrVars :: Monad m => [(Id, Int)] -> [StrTem] -> GenM1 m ([[Id]], Code)
--createArrVars ndims arrVid pats = 

-- TODO: change to treat non 0,0 aligned subarrays properly.
-- |eqJoinArr template
t4 :: Monad m => Template m
t4 (Tup [(Lf (ListTy int1)), 
         (Lf (ListTy int2)),
         (Lf (LfTy "DistArr" [ty1, ty2, inLay1,  inLay11,  inPart1,  inDims1,  Lf (LfTy "MirrDims" inMirrs1 )])),
         (Lf (LfTy "DistArr" [ty3, ty4, inLay2,  inLay12,  inPart2,  inDims2,  Lf (LfTy "MirrDims" inMirrs2 )]))] :-> 
   outT@(Lf (LfTy "DistArrStream" [ty5, ty6, outLay, outLay1, outPart, outDims, Lf (LfTy "MirrDims" outMirrs)])))
   (LFun _ (LTup _ [idxs1, idxs2, in1, in2]) out) = do -- TODO add type checks
    -- get int lists from literal tuples
    eqIndices1 <- getLitIntList idxs1
    eqIndices2 <- getLitIntList idxs2
    -- get other indices 
    let numIndices1 = length $ flattenTree ty1
    let numIndices2 = length $ flattenTree ty3
    let totNumIndices = numIndices1 + numIndices2
    let allIndices1 = [0..numIndices1-1]
    let allIndices2 = [0..numIndices2-1]
    let remIndices1 = allIndices1 \\ eqIndices1
    let remIndices2 = allIndices2 \\ eqIndices2
    -- maps virtual (high level) indices to physical indices and visa versa
    let idxMap1 = appLayout inLay1 allIndices1 
    let idxMap2 = appLayout inLay2 allIndices2
    -- translate virtual eqIndices to physical ones 
    let transIndices = \idxMap -> \idxs -> map (\i -> idxMap !! i) idxs
    let pEqIndices1 = transIndices idxMap1 eqIndices1
    let pEqIndices2 = transIndices idxMap2 eqIndices2
    let pRemIndices1 = transIndices idxMap1 remIndices1
    let pRemIndices2 = transIndices idxMap2 remIndices2
    let pEqIndices = zip pEqIndices1 pEqIndices2
   -- error $ "eqJoinArr:\n\n" ++ (show $ zip eqIndices1 eqIndices2) ++ "\n\n" ++ (show pEqIndices) ++ "\n\n" ++ (show $ remIndices1 ++ remIndices2) ++ "\n\n" ++ (show $ pRemIndices1 ++ pRemIndices2) ++ "\n"
    -- get var names of input arrays
    getVar (Lf "in1") in1 outVarName
    getVar (Lf "in2") in2 outVarName
    genTrace "eqJoinArr got input vars\n"
    let arr1 = ("a", brak "in1")
    let arr2 = ("a", brak "in2")
    (elemsVar1,decElems1) <- genScalVar (Lf $ LfTy "Ptr" [ty2]) "<a>.parent->elems" [("a", "<in1>")]
    (elemsVar2,decElems2) <- genScalVar (Lf $ LfTy "Ptr" [ty4]) "<a>.parent->elems" [("a", "<in2>")]
    let decElems = decElems1 ++ decElems2
    -- generate bounds vars for all PHYSICAL indices
    let pl = map fst
    parStart1s <- mapM (genScalVar intTy "<a>.parent->getDimStart(<i>)") $ map (\i -> [arr1, ("i", show i)]) allIndices1  
    parStart2s <- mapM (genScalVar intTy "<a>.parent->getDimStart(<i>)") $ map (\i -> [arr2, ("i", show i)]) allIndices2 
    start1s <- mapM (genScalVar intTy "<a>.getDimStart(<i>)") $ map (\i -> [arr1, ("i", show i)]) allIndices1  
    start2s <- mapM (genScalVar intTy "<a>.getDimStart(<i>)") $ map (\i -> [arr2, ("i", show i)]) allIndices2 
    last1s <- mapM (genScalVar intTy "<a>.getDimEnd(<i>)") $ map (\i -> [arr1, ("i", show i)]) allIndices1  
    last2s <- mapM (genScalVar intTy "<a>.getDimEnd(<i>)") $ map (\i -> [arr2, ("i", show i)]) allIndices2 
    end1s <- mapM (genScalVar intTy "<l>+1") $ map (\l -> [arr1, ("l", brak l)]) $ pl last1s
    end2s <- mapM (genScalVar intTy "<l>+1") $ map (\l -> [arr2, ("l", brak l)]) $ pl last2s 
    let endVars1 = pl end1s
    let endVars2 = pl end2s
    parLen1s <- mapM (genScalVar intTy "<a>.parent->getDimSize(<i>)") $ map (\i -> [arr1, ("i", show i)]) allIndices1  
    parLen2s <- mapM (genScalVar intTy "<a>.parent->getDimSize(<i>)") $ map (\i -> [arr2, ("i", show i)]) allIndices2 
    len1s <- mapM (genScalVar intTy "<a>.getDimSize(<i>)") $ map (\i -> [arr1, ("i", show i)]) allIndices1  
    len2s <- mapM (genScalVar intTy "<a>.getDimSize(<i>)") $ map (\i -> [arr2, ("i", show i)]) allIndices2 
    --zeros1 <- mapM (\_ -> genScalVar intTy "0" []) allIndices1
    --zeros2 <- mapM (\_ -> genScalVar intTy "0" []) allIndices2
    let boundsCode = concatProj snd [parStart1s, parStart2s, start1s, start2s, last1s, last2s, end1s, end2s, parLen1s, parLen2s, len1s, len2s{-, zeros1, zeros2-}]
    -- generate steps for loops (PHYSICAL indices)
    (steps1',_,steps1Code) <- foldM (\(lst,accExp,accCode) -> \l ->
      do (i,c) <- genScalVar intTy "<l>" [("l",accExp)] ; 
         return (i:lst,(brak i)++"*"++l,accCode++c) ) ([], "1","") $ reverse $ map (brak.fst) parLen1s
    let steps1 = steps1'
    (steps2',_,steps2Code) <- foldM (\(lst,accExp,accCode) -> \l ->
      do (i,c) <- genScalVar intTy "<l>" [("l",accExp)] ; 
         genTrace ("made var " ++ (show i) ++ " dec called " ++ (show c) ++ " l is " ++ (show l) ++ " with val " ++ accExp ++ "\ndec code is " ++ accCode++c) ;
         return (i:lst,(brak i)++"*"++l,accCode++c) ) ([], "1","") $ reverse $ map (brak.fst) parLen2s
    let steps2 = steps2'
    let step1Var = head $ reverse $ steps1
    let stepsCode = steps1Code ++ steps2Code
    -- generate PHYSICAL idx begins ((subArrStart-parArrStart)*stepsize) and limits ((subArrEnd-parArrStart)*stepsize)
    begin1s <- mapM (\(saSt,pSt,step) -> genScalVar intTy "(<saSt>-<pSt>)*<step>" 
                  [("saSt",brak saSt),("pSt", brak pSt),("step", brak step)]) $ zip3 (pl start1s) (pl parStart1s) steps1
    begin2s <- mapM (\(saSt,pSt,step) -> genScalVar intTy "(<saSt>-<pSt>)*<step>" 
                  [("saSt",brak saSt),("pSt", brak pSt),("step", brak step)]) $ zip3 (pl start2s) (pl parStart2s) steps2
    lim1s <- mapM (\(s,e,pSt) -> genScalVar intTy "<s>*(<e>-<pSt>)" [("s", brak s), ("e", brak e), ("pSt", brak pSt)]) $ zip3 steps1 (pl end1s) (pl parStart1s)
    lim2s <- mapM (\(s,e,pSt) -> genScalVar intTy "<s>*(<e>-<pSt>)" [("s", brak s), ("e", brak e), ("pSt", brak pSt)]) $ zip3 steps2 (pl end2s) (pl parStart2s)
    let limDecs = concatProj snd [begin1s, begin2s, lim1s, lim2s]
    -- generate PHYSICAL idx and it vars
    indices1 <- mapM (\_ -> genScalVar intTy "0" []) allIndices1
    indices2 <- mapM (\_ -> genScalVar intTy "0" []) allIndices2
    itStarts1 <- mapM (genScalVar intTy "<i>+<st>") 
      $ map (\(i,s) -> [("i", brak $ fst i), ("st", brak $ fst s)]) $ zip indices1 start1s 
    let (itStartVars1,_) = unzip itStarts1
    itStarts2 <- mapM (genScalVar intTy "<i>+<st>") 
      $ map (\(i,s) -> [("i", brak $ fst i), ("st", brak $ fst s)]) $ zip indices2 start2s 
    let (itStartVars2,_) = unzip itStarts2
    its1 <- mapM (genScalVar intTy "<st>") $ map (\s -> [("st", brak s)]) itStartVars1 
    let (itVars1,_) = unzip its1 
    its2 <- mapM (genScalVar intTy "<st>") $ map (\s -> [("st", brak s)]) itStartVars2
    let (itVars2,_) = unzip its2
    let itsCode = concatProj snd [indices1, indices2, itStarts1, itStarts2, its1, its2]
    -- generate eq index bounds for VIRTUAL INDICES
    --let eqIndices = zip eqIndices1 eqIndices2
    {-eqStarts <- mapM (genScalVar intTy "MAX(<i>,<j>)") 
      $ map (\(i,j) -> [("i", brak $ fst $ start1s !! (idxMap1 !! i)),("j", brak $ fst $ start2s !! (idxMap2 !! j))]) eqIndices
    eqEnds <- mapM (genScalVar intTy "MIN(<i>,<j>)") 
      $ map (\(i,j) -> [("i", brak $ fst $ last1s !! (idxMap1 !! i)),("j", brak $ fst $ last2s !! (idxMap2 !! j))]) eqIndices
    eq1Starts <- mapM (genScalVar intTy "<mx>-<st>") 
      $ map (\(mx,i) -> [("mx", brak $ fst mx), ("st", brak $ fst $ (start1s !! (idxMap1 !! i)))]) $ zip eqStarts eqIndices1 
    eq2Starts <- mapM (genScalVar intTy "<mx>-<st>") 
      $ map (\(mx,i) -> [("mx", brak $ fst mx), ("st", brak $ fst $ (start2s !! (idxMap2 !! i)))]) $ zip eqStarts eqIndices2
    eq1Ends <- mapM (genScalVar intTy "<mn>-<st>") 
      $ map (\(mn,i) -> [("mn", brak $ fst mn), ("st", brak $ fst $ (last1s !! (idxMap1 !! i)))]) $ zip eqEnds eqIndices1 
    eq2Ends <- mapM (genScalVar intTy "<mn>-<st>") 
      $ map (\(mn,i) -> [("mn", brak $ fst mn), ("st", brak $ fst $ (last2s !! (idxMap2 !! i)))]) $ zip eqEnds eqIndices2
    let boundsCode2 = concatProj snd [eqStarts, eqEnds, eq1Starts, eq2Starts, eq1Ends, eq2Ends]-}
    -- generate loops over PHYSICAL indices -- (idxVars, startVars, endVars, stepVars)
    -- (each loop iterates over idx vars for arr access, and it vars too)
    let allLoopVars1 = map (\line -> [line]) $ zip4 (pl indices1) (pl begin1s) (pl lim1s) steps1
    let allLoopVars2 = map (\line -> [line]) $ zip4 (pl indices2) (pl begin2s) (pl lim2s) steps2
    let outLoopVars1 = map (\i -> (allLoopVars1 !! i) ++ [(itVars1 !! i, itStartVars1 !! i, endVars1 !! i, step1Var)]) pRemIndices1 -- it1 vars
    let outLoopVars2 = map (\i -> (allLoopVars2 !! i) ++ [(itVars2 !! i, itStartVars2 !! i, endVars2 !! i, step1Var)]) pRemIndices2
    let eqLoopVars = map (\(i1,i2) -> (allLoopVars1 !! i1) ++ (allLoopVars2 !! i2)
            ++ [(itVars1 !! i1, itStartVars1 !! i1, endVars1 !! i1, step1Var)]
            ++ [(itVars2 !! i2, itStartVars2 !! i2, endVars2 !! i2, step1Var)]) pEqIndices
    -- (generate print indices debug helper)
    prints1 <- mapM (\(dim,l) -> genDebugLoop "outer1" (show dim) l) $ zip pRemIndices1 outLoopVars1
    prints2 <- mapM (\(dim,l) -> genDebugLoop "outer2" (show dim) l) $ zip pRemIndices2 outLoopVars2
    prints3 <- mapM (\(dim,l) -> genDebugLoop "inner" (show dim) l) $ zip pEqIndices eqLoopVars
    loops <- mapM genArrLoop $ outLoopVars1 ++ outLoopVars2 ++ eqLoopVars
    let loops' = (prints1 ++ prints2 ++ prints3) ++ loops
    --let loops' = alternate loops (prints1 ++ prints2 ++ prints3) 
    -- generate element accessors for body using PHYSICAL indices
    -- (just sum the steps to get the offset)
    let idxExp1 = concat $ intersperse " + " $ map brak $ pl indices1
    let idxExp2 = concat $ intersperse " + " $ map brak $ pl indices2
    (valVar1,decVal1) <- genScalVar ty2 ("<e>["++idxExp1++"]") [("e",brak elemsVar1)]
    (valVar2,decVal2) <- genScalVar ty4 ("<e>["++idxExp2++"]") [("e",brak elemsVar2)]
    let loopVals = [(decVal1++decVal2, "")]
    -- translate PHYSICAL bounds and indices to VIRTUAL ones
    -- (for each virtual index pick corresponding physical variable)
    -- (TODO make use inverse layout function)
    let vIts1 = map (\vi -> its1 !! (idxMap1 !! vi)) allIndices1
    let vIts2 = map (\vi -> its2 !! (idxMap2 !! vi)) allIndices2
    let vStarts1 = map (\vi -> start1s !! (idxMap1 !! vi)) allIndices1
    let vStarts2 = map (\vi -> start2s !! (idxMap2 !! vi)) allIndices2
    let vLasts1 = map (\vi -> last1s !! (idxMap1 !! vi)) allIndices1
    let vLasts2 = map (\vi -> last2s !! (idxMap2 !! vi)) allIndices2
    let vLens1 = map (\vi -> len1s !! (idxMap1 !! vi)) allIndices1
    let vLens2 = map (\vi -> len2s !! (idxMap2 !! vi)) allIndices2
    --error $ "eqJoinArr:\n\n" ++ (show $ its1 ++ its2) ++ "\n\n" ++ (show $ vIts1 ++ vIts2) ++ "\n\n"
    -- pass VIRTUAL bounds and VIRTUAL it vars to consumers
    setVar out "streamVar" (Tup [Tup (map ((Lf).fst) $ vIts1 ++ vIts2), Tup [Lf valVar1, Lf valVar2]])
    setVar out "streamIdxStarts" $ Tup (map ((Lf).fst) $ vStarts1 ++ vStarts2)
    setVar out "streamIdxEnds" $ Tup (map ((Lf).fst) $ vLasts1 ++ vLasts2)
    setVar out "streamIdxLens" $ Tup (map ((Lf).fst) $ vLens1 ++ vLens2)
    -- create generator function
    setFun out "gen" nt (\_ -> do
       -- generate stream consumer code blocks
      genTrace "entered eqJoinArr.gen"
      -- (TODO pass bounds/make bounds available to consumers for array streams)
      callAll out "genConsumers" nt
      getCode "init" out "initStream"
      getCode "fin" out "finStream"
      getCode "consume" out "consumers"
      -- generate loop code
      let loopCode = nestCode $ loops' ++ loopVals ++ [("<consume>", "")]
      -- output code
      output "main" $ 
            "\n\n//begin eqJoinArr\n" ++ 
            boundsCode ++ {-boundsCode2 ++ -}
            stepsCode ++ itsCode ++ limDecs ++
            decElems ++ 
            "<init>\n" ++   
            loopCode ++ 
            "<fin>\n" ++
            "\n//end eqJoinArr\n"
      return ())
t4 t n = terr "eqJoinArr" t n

-- TODO fix the below
--   remembering eqIndices need to be translated from 
--   arr1 offsets to arr2 offsets. or just iterated over 
--   seperately in the loop?

-- |eqJoinArr template
{-t4 :: Monad m => Template m
t4 (Tup [(Lf (ListTy int1)), 
         (Lf (ListTy int2)),
         (Lf (LfTy "DistArr" [ty1, ty2, inLay1,  inLay11,  inPart1,  inDims1,  Lf (LfTy "MirrDims" inMirrs1 )])),
         (Lf (LfTy "DistArr" [ty3, ty4, inLay2,  inLay12,  inPart2,  inDims2,  Lf (LfTy "MirrDims" inMirrs2 )]))] :-> 
   outT@(Lf (LfTy "DistArrStream" [ty5, ty6, outLay, outLay1, outPart, outDims, Lf (LfTy "MirrDims" outMirrs)])))
   (LFun _ (LTup _ [idxs1, idxs2, in1, in2]) out) = do -- TODO add type checks
    -- get int lists from literal tuples
    eqIndices1 <- getLitIntList idxs1
    eqIndices2 <- getLitIntList idxs2
    -- get other indices 
    let numIndices1 = length $ flattenTree ty1
    let numIndices2 = length $ flattenTree ty3
    let totNumIndices = numIndices1 + numIndices2
    let allIndices1 = [0..numIndices1-1]
    let allIndices2 = [0..numIndices2-1]
    let remIndices1 = allIndices1 \\ eqIndices1
    let remIndices2 = allIndices2 \\ eqIndices2
    -- get var names of input arrays
    getVar (Lf "in1") in1 outVarName; (VarV _ (Lf in1Vid)) <- getLocalVal "in1"
    getVar (Lf "in2") in2 outVarName; (VarV _ (Lf in2Vid)) <- getLocalVal "in2"
    -- generate vars for loops
    mapM (\n -> newVar (Lf n) uintTy) $ (map (("in1Idx"++).show) allIndices1) ++ (map (("in2Idx"++).show) allIndices2)
    newVar (Lf $ "inIt") intTy
    newVar (Lf $ "inIt2") intTy
    varExp "itSz" "" ("(" ++ in1Vid ++ ".numDims()" ++ " + " ++ in2Vid ++ ".numDims())") uintTy
    runGenV "declareArr" "decIt" [Lf "inIt", Lf "itSz"]
    runGenV "declareArr" "decIt2" [Lf "inIt2", Lf "itSz"]
    idxCopies <- mapM (\(srcIdx, dstIdx) -> -- copy indices to index into 2nd array
      let n = "copyIt"++(show srcIdx)++"to"++(show dstIdx) in
      let n2 = "copyIdx"++(show srcIdx)++ "to" ++ (show dstIdx) in
      let s = ("srcIdx"++(show srcIdx)) in
      let d = ("dstIdx"++(show dstIdx)) in
      do varExp s "inIt" ("<v>["++(show srcIdx)++"]") intTy ;
         varExp d "inIt2" ("<v>["++(show dstIdx)++"]") intTy ;
         runGenV "assignVar" n [Lf d, Lf s] ; 
         --runGenV "declareVarInit" n2 [Lf ("in2Idx"++(show srcIdx)), ] ; 
         return $ "<"++n++">" ) $ zip [numIndices1..] allIndices2
    mapM (\dim -> let i = show dim in varExp ("in1It" ++ i) "inIt" ("<v>[" ++ i ++ "]") intTy) allIndices1
    mapM (\dim -> varExp ("in2It" ++ (show dim)) "inIt" ("<v>[" ++ (show $ dim+numIndices1) ++ "]") intTy) allIndices2 
    --newVar (Lf $ "in1It") intTy
    --newVar (Lf $ "in2It") intTy
    --varExp "in1Dims" "in1" "<v>.numDims()" uintTy
    --varExp "in2Dims" "in2" "<v>.numDims()" uintTy
    --runGenV "declareArr" "decIt1" [Lf "in1It", Lf "in1Dims"]
    --runGenV "declareArr" "decIt2" [Lf "in2It", Lf "in2Dims"]
    --mapM (\dim -> varExp ("in1It" ++ (show dim)) "in1It" ("<v>[" ++ (show dim) ++ "]") intTy) allIndices1 
    --mapM (\dim -> varExp ("in2It" ++ (show dim)) "in2It" ("<v>[" ++ (show dim) ++ "]") intTy) allIndices2
    -- get bounds either from templates, or using getDimX functions
    --                                        arrNode boundId arrName methName ty indices
    (startns1, startVids1) <- getArrBounds in1 "arrayStarts" "in1" "getDimStart" intTy allIndices1
    (startns2, startVids2) <- getArrBounds in2 "arrayStarts" "in2" "getDimStart" intTy allIndices2
    (endNames1, endVids1) <- getArrBounds in1 "arrayEnds" "in1" "getDimEnd" intTy allIndices1
    (endNames2, endVids2) <- getArrBounds in2 "arrayEnds" "in2" "getDimEnd" intTy allIndices2
    -- generate index loops (TODO change to iter vars are created using varExp to make int arrays)
    -- outer loops
    let startPatOut = "<arr>.getDimStart(<dim>)"
    let endPatOut = "<arr>.getDimEnd(<dim>)"
    --                         arrVid startVids endVids startns itns indices
    let in1IdxVNames = (map (Lf.("in1Idx"++).show) allIndices1)
    let in1ItVNames = (map (Lf.("in1It"++).show) allIndices1)
    outerLoops1 <- genArrLoops in1Vid startVids1 endVids1 startns1 in1IdxVNames in1ItVNames remIndices1 
    let (outerDecls1, outerLoops1') = unzip outerLoops1 
    let in2IdxVNames = (map (Lf.("in2Idx"++).show) allIndices2)
    let in2ItVNames = (map (Lf.("in2It"++).show) allIndices2)
    outerLoops2 <- genArrLoops in2Vid startVids2 endVids2 startns2 in2IdxVNames in2ItVNames remIndices2 
    let (outerDecls2, outerLoops2') = unzip outerLoops2
    --error $ show $ (zip startVids1 endVids1) ++ (zip startVids2 endVids2)
    -- inner loops (iterate over intersection, and assign eq indices in in1It to corresponding in in2It)
    let startPatIn = "MAX(<a1>.getDimStart(<d1>), <a2>.getDimStart(<d2>))"
    let endPatIn = "MIN(<a1>.getDimEnd(<d1>), <a2>.getDimEnd(<d2>))"
    let beginPat = " = <it>;\n"
    innerLoops <- mapM (\(d1,d2) -> do
      (VarV _ (Lf itVid2)) <- getLocalVal ("in2It"++(show d2)) ;
      genArrIdxLoop (itVid2 ++ " = <it>;\n") startPatIn endPatIn 
                    ("in1Idx"++(show d1)) ("in1It"++(show d1)) 
        [("d1",show d1),("d2", show d2),("a1",in1Vid),("a2",in2Vid)] ) $ zip eqIndices1 eqIndices2
    let (innerDecls, innerLoops') = unzip innerLoops
    -- create value vars and assign from arrays
    newVar (Lf "ndims1") uintTy
    varExp "ndims1a" "in1" "<v>.numDims()" uintTy
    runGenV "declareVarInit" "decNDims1" [Lf "ndims1", Lf "ndims1a"]
    (VarV _ (Lf nDims1Vid)) <- getLocalVal "ndims1"
    newVar (Lf "val1") ty2
    newVar (Lf "val2") ty4
    runGenV "declareVar" "decVal1" [Lf "val1"]
    runGenV "declareVar" "decVal2" [Lf "val2"]
    -- old:
    --varExp "arr1Val" "inIt" (in1Vid ++ "[<v>]") ty2 
    --varExp "arr2Val" "inIt2" (in2Vid ++ "[<v>]") ty4
    -- new:
    let startIdxs1 = map (\idx -> in1Vid ++ ".getDimStart(" ++ (show idx) ++ ")") allIndices1
    let startIdxs2 = map (\idx -> in2Vid ++ ".getDimStart(" ++ (show idx) ++ ")") allIndices2
    let startIdxs = startIdxs1 ++ startIdxs2
    --(VarV _ (Lf inItVid)) <- getLocalVal "inIt"
    --let idxList1 = map (\idx -> inItVid ++ "[" ++ (show idx) ++ "]-" ++ (startIdxs !! idx)) allIndices1
    --let idxList2 = map (\idx -> inItVid ++ "[" ++ (show idx) ++ "]-" ++ (startIdxs !! idx)) [numIndices1..totNumIndices-1]
    idxList1 <- mapM (\dim -> do 
                       (VarV _ (Lf itVid)) <- getLocalVal (treeLeaf "eqJoinArr1" $ in1ItVNames !! dim); 
                       (VarV _ (Lf idxVid)) <- getLocalVal (treeLeaf "eqJoinArr2" $ in1IdxVNames !! dim); 
                       return $ "(" ++ idxVid ++ (if dim < (numIndices1-1) then "*"++(escapeStr itVid)++"Len" else "") ++ ")") allIndices1
    idxList2 <- mapM (\dim -> do 
                       (VarV _ (Lf itVid)) <- getLocalVal (treeLeaf "eqJoinArr3" $ in2ItVNames !! dim); 
                       (VarV _ (Lf idxVid)) <- getLocalVal (treeLeaf "eqJoinArr4" $ in2IdxVNames !! dim); 
                       return $ "(" ++ idxVid ++ (if dim < (numIndices2-1) then "*"++(escapeStr itVid)++"Len" else "") ++ ")") allIndices2
    varExp "inIdxs1" "" (concat $ intersperse "+" idxList1) nullTy
    varExp "inIdxs2" "" (concat $ intersperse "+" idxList2) nullTy
    varExp "arr1Val" "inIdxs1" (in1Vid ++ ".parent->elems[<v>]") ty2
    varExp "arr2Val" "inIdxs2" (in2Vid ++ ".parent->elems[<v>]") ty4
    ----------
    runGenV "assignVar" "copyVal1" [Lf "val1", Lf "arr1Val"] -- get elements from array
    runGenV "assignVar" "copyVal2" [Lf "val2", Lf "arr2Val"] 
    -- set stream var(s)
    inItns <- mapM (\idx -> let name = "inIt" ++ (show idx) in 
      do varExp name "inIt" ("<v>[" ++ (show idx) ++ "]") intTy ; return $ Lf name) $ [0..totNumIndices-1]
    setVar out "streamVar" (Tup [Tup inItns, Tup [Lf "val1", Lf "val2"]])
    let arrIdxList = zip [0..] $ (zip (repeat in1Vid) allIndices1) ++ (zip (repeat in2Vid) allIndices2)
    startIdxNames <- mapM (\(oidx,(arr,aidx)) -> let n = "idxStart"++(show oidx) in 
      do varExp n "" (arr++".getDimStart("++(show aidx)++")") intTy ; return $ Lf n ) arrIdxList
    setVar out "streamIdxStarts" $ Tup startIdxNames
    endIdxNames <- mapM (\(oidx,(arr,aidx)) -> let n = "idxEnd"++(show oidx) in 
      do varExp n "" (arr++".getDimEnd("++(show aidx)++")") intTy ; return $ Lf n ) arrIdxList
    setVar out "streamIdxEnds" $ Tup endIdxNames
    lenIdxNames <- mapM (\(oidx,(arr,aidx)) -> let n = "idxLen"++(show oidx) in 
      do varExp n "" (arr++".getDimSize("++(show aidx)++")") intTy ; return $ Lf n ) arrIdxList
    setVar out "streamIdxLens" $ Tup lenIdxNames
    -- generate 
    setFun out "gen" nt (\_ -> do
       -- generate stream consumer code blocks
      genTrace "entered eqJoinArr.gen"
      -- (TODO pass bounds/make bounds available to consumers for array streams)
      callAll out "genConsumers" nt
      getCode "init" out "initStream"
      getCode "fin" out "finStream"
      getCode "consume" out "consumers"
      -- generate loop code
      let initFinCode = [("<decVal1><decVal2>const <decNDims1>\n<init>", "<fin>")] 
      let declsCode = map (\s -> (s,"")) $ outerDecls1 ++ outerDecls2 ++ innerDecls
      let consumeCode = [((concat idxCopies)++"<copyVal1><copyVal2><consume>", "")]
      let loopCode = nestCode $ initFinCode ++ declsCode ++ outerLoops1' ++ outerLoops2' ++ innerLoops' ++ consumeCode
      output "main" $ "// eqJoinArr: " ++ (show remIndices1) ++ "; " ++ (show remIndices2) ++ "\n" ++ {-"<decIt1><decIt2>"-} "<decIt><decIt2>" ++ loopCode
      return ())
t4 t n = terr "eqJoinArr" t n-}

-- mapArrStream template
t9 :: Monad m => Template m 
t9 (Tup [Tup [idxTy, inValTy] :-> outValTy,
         Lf (LfTy "DistArrStream" [idxT1, inVT1, _, _, _, distDims1, mirrDims1])] :-> 
         Lf (LfTy "DistArrStream" [idxT2, outVT1, _, _, _, distDims2, mirrDims2]))
   (LFun _ (LTup _ [vf, input]) out) 
   | match idxTy [idxT1, idxT2] && inValTy == inVT1 && outValTy == outVT1 = do
   -- sanity check
   assertM (return $ distDims1 == distDims2) "mapArrStream: partition dims don't match"
   assertM (return $ mirrDims1 == mirrDims2) "mapArrStream: mirror dims don't match"
   -- get producer's stream vars (VIRTUAL INDICES)
   getVar (Tup [Lf "inIdx", Lf "inVal"]) input "streamVar"
   getVar (Lf "streamIdxStarts") input "streamIdxStarts"
   getVar (Lf "streamIdxEnds") input "streamIdxEnds"
   getVar (Lf "streamIdxLens") input "streamIdxLens"
   -- create consumer stream var
   newVar (Lf "outVal") outValTy
   -- set stream var for b
   setVar out "streamVar" (Tup [Lf "inIdx", Lf "outVal"])
   setVar out "streamIdxStarts" $ Lf "streamIdxStarts"
   setVar out "streamIdxEnds" $ Lf "streamIdxEnds"
   setVar out "streamIdxLens" $ Lf "streamIdxLens"
   -- def "genConsumers" to generate consumers
   setFun out "genConsumers" nt (\_ -> do
     genTrace "entered mapArrStream.genConsumers"
     -- generate outs declaration
     runGenV "declareVar" "decOuts" [Lf "outVal"]
     -- generate map fun implementation
     genFunV "vfCode" vf (Tup [Lf "inIdx", Lf "inVal"]) (Lf "outVal")
     -- generate b's consumers
     callAll out "genConsumers" nt
     getCode "consume" out "consumers"
     getCode "init" out "initStream"
     getCode "fin" out "finStream"
     -- add these consumers to parent
     addCode input "consumers" "// mapArrStream:\n//decOuts\n<decOuts>//vfCode\n<vfCode>\n//consume:\n<consume>\n"
     addCode input "initStream" "<init>"
     addCode input "finStream" "<fin>"
     )
   return ()
t9 t n = terr "mapArrStream" t n

-- |groupReduceArrStream template
-- |WARNING: Only works if collapsing dims can be done locally, i.e. whole
-- |strips of the dimensions to reduce exist locally at this node.
t12 :: Monad m => Template m
t12 ((Tup [outIdxTy,
          (Tup [inIdxTy, inValTy] :-> outValTy),
          (Tup [outVT1, outVT2] :-> outVT3),
          outVT4, 
          Lf (LfTy "DistArrStream" [inIT2, inVT2, inLay, inLayInv, t3, inDims, mirrDims1])
         ])
     :-> outT@(Lf (LfTy "DistArr" arrTyParams@[outIT2, outVT5, outLay, outLayInv, t6, outDims, mirrDims2])))
   (LFun _ (LTup _ [kf,pf,rf,v0,ins]) out)
   | match nullFun [t3,t6] && mirrDims1 == mirrDims2 &&
     outIdxTy == outIT2 && inIdxTy == inIT2 && inValTy == inVT2 &&
     match outValTy [outVT1, outVT2, outVT3, outVT4, outVT5] = do
   -- count number of output indices
   let numInIndices = length $ flattenTree inIdxTy
   varExp "numInDims" "" (show numInIndices) uintTy
   let numOutIndices = length $ flattenTree outIdxTy
   varExp "numOutDims" "" (show numOutIndices) uintTy
   keyIndices <- getLitIntList kf
   -- get input stream vars (VIRTUAL indices)
   getVar (Lf "svar") ins "streamVar"
   aliasVar (Tup [Lf "sidx", Lf "sval"]) (Lf "svar")
   getVar (Lf "arrStarts") ins "streamIdxStarts"
   getVar (Lf "arrEnds") ins "streamIdxEnds"
   getVar (Lf "arrLens") ins "streamIdxLens"
   -- get sizes of input array dims
   let startVNames = map (\n -> "startV"++(show n)) [0..numInIndices-1]
   let endVNames = map (\n -> "endV"++(show n)) $ [0..numInIndices-1] 
   aliasVar (Tup $ map Lf startVNames) (Lf "arrStarts")
   aliasVar (Tup $ map Lf endVNames) (Lf "arrEnds")
   lenExps <- mapM (\idx -> let n = "len"++(show idx) in 
     do (VarV _ (Lf endVid)) <- getLocalVal (endVNames !! idx) ;
        varExp n (startVNames !! idx) ("(" ++ endVid ++ "-(<v>)+1)") uintTy ; 
        return $ Lf n) $ keyIndices
   startExps <- mapM (\idx -> let n = "start"++(show idx) in 
     do varExp n (startVNames !! idx) ("(<v>)") intTy ; 
        return $ Lf n) $ keyIndices
   -- declare output val scalars
   newVar (Lf "val1") outValTy
   newVar (Lf "val2") outValTy
   -- declare output array size
   newVar (Lf $ "lens") uintTy
   newVar (Lf $ "starts") intTy
   runGenV "declareArr" "decLens" [Lf "lens", Lf "numOutDims"]
   runGenV "declareArr" "decStarts" [Lf "starts", Lf "numOutDims"]
   lenDests <- mapM (\(srcIdx, dstIdx) -> let n = "lenDest"++(show dstIdx) in 
     do varExp n "lens" ("<v>["++(show dstIdx)++"]") uintTy ; return $ Lf n  ) $ zip keyIndices [0..]
   startDests <- mapM (\(srcIdx, dstIdx) -> let n = "startDest"++(show dstIdx) in 
     do varExp n "starts" ("<v>["++(show dstIdx)++"]") intTy ; return $ Lf n  ) $ zip keyIndices [0..]
   runGenV "assignVar" "copyLens" [Tup lenDests, Tup lenExps]
   runGenV "assignVar" "copyStarts" [Tup startDests, Tup startExps]
   -- OLD: declare output array 
   {-varExp "mpiFloat" "" "MPI::DOUBLE" nullTy -- TODO call getMPITypeName
   ifnVarInit "decArr" outVarName (Lf "arr") outT (Just $ Tup [Lf "mpiFloat", Lf "lens", Lf "starts"])-}
   -- NEW: declare output array
   newVar (Lf "buffer") (Lf $ LfTy "Ptr" [outValTy])
   (VarV _ (Lf bufVid)) <- getLocalVal "buffer"
   mbElTn <- genTypeName outValTy
   let vTn = fromMaybe (error $ "ArrTemplates:groupReduceArrStream: cant gen name for array element type " ++ (show outValTy) ++ "!\n") mbElTn
   let decBuffer = "static " ++ vTn ++ " " ++ bufVid ++ "[5000*5000*2];\n"; -- TODO change to get max sizes from input
   newVar (Lf "mpiTy") mpiTyTy
   runGenV "genMPITyName" "decMPITy" [Lf "val1", Lf "mpiTy"]
   let rootArrTy = (Lf $ LfTy "DistArrRoot" arrTyParams)
   newVar (Lf "rootArr") rootArrTy
   runGenV "declareVarInit" "decRootArr" [Lf "rootArr", Tup [Lf "mpiTy", Lf "lens", Lf "starts", Lf "buffer"]]
   varExp "rootArrPtr" "rootArr" "(&<v>)" (Lf $ LfTy "Ptr" [rootArrTy])
   ifnVarInit "decArr" outVarName (Lf "arr") outT (Just $ Tup [Lf "rootArrPtr", Lf "lens", Lf "starts"]) 
   -- init output array
   getVar (Lf "initVal") v0 outVarName
   newVar (Lf "it") (Lf $ LfTy "Iter" [outT])
   newVar (Lf "itEnd") (Lf $ LfTy "Iter" [outT])
   varExp "arrBegin" "arr" "<v>.begin()" (Lf $ LfTy "Iter" [outT])
   varExp "arrEnd" "arr" "<v>.end()" (Lf $ LfTy "Iter" [outT])
   runGenV "declareVarInit" "decIt" [Lf "it", Lf "arrBegin"]
   runGenV "declareVarInit" "decItEnd" [Lf "itEnd", Lf "arrEnd"]
   varExp "itVal" "it" "(*<it>)" outValTy
   runGenV "assignVar" "copyInitVal" [Lf "itVal", Lf "initVal"]
   let initArr = "// init array\n<decIt><decItEnd>\n"++
                 "for (; <it> != <itEnd>; <it>++) {<copyInitVal>}\n"
   -- make dest array var
   newVar (Lf $ "idx") intTy
   runGenV "declareArr" "decIdx" [Lf "idx", Lf "numOutDims"]
   let sidxNames = map (\idx -> Lf $ "sidx" ++ (show idx)) [0..numInIndices-1] 
   aliasVar (Tup sidxNames) (Lf "sidx")
   let sidxNames' = map (\idx -> sidxNames !! idx) keyIndices
   idxNames <- mapM (\idx -> let n = "idx"++(show idx) in 
     do varExp n "idx" ("<v>["++(show idx) ++"]") intTy ; return $ Lf n) [0..numOutIndices-1]   
   runGenV "assignVar" "copyIdxs" [Tup idxNames, Tup sidxNames']
   (VarV _ (Lf idxVid)) <- getLocalVal "idx"
   varExp "arrVal" "arr" ("<v>["++idxVid++"]") outValTy
   -- NEW: make indices that start from 0
   let tl = treeLeaf "groupRedArrStm:1"
   zeroIdxs <- mapM (\i -> do varExp ("zidx"++(show i)) (startVNames !! i) ("("++(brak $ tl $ sidxNames !! i) ++ "-<v>)") intTy ; return ("zidx"++(show i))) [0..numInIndices-1] 
   -- NEW: make array len vars
   lenVals' <- mapM (\(s,e) -> genScalVar intTy "<e>-<s>+1" [("s",brak s),("e", brak e)]) $ zip startVNames endVNames
   let (lenVars,_) = unzip lenVals'
   let decLens2 = concatProj snd [lenVals']
   -- NEW: make pointer to underlying array
   (VarV _ (Lf arrVid)) <- getLocalVal "arr"
   (_,decElems) <- genScalVar (Lf $ LfTy "Ptr" [outVT1]) (arrVid++".parent->elems") []
   let (elemsVar, decElems) = ("buffer", "") -- CHANGED TO WRITE TO BUFFER
   -- NEW: make arr offset expression
   let (hdKey:tailKeys) = keyIndices
   let offExp = foldl (\exp -> \i -> "(" ++ (brak $ zeroIdxs !! i) ++ " + (" ++ (brak $ lenVars !! i) ++ " * " ++ exp ++ "))" ) (brak $ zeroIdxs !! 0) tailKeys
   offExp' <- expandTem offExp
   (offVal,decOffVal) <- genScalVar intTy offExp' []
   varExp "arrVal'" elemsVar ("<v>["++(brak offVal)++"]") outValTy
   -- project out and combine vals
   runGenV "declareVar" "decVals" [Tup [Lf "val1", Lf "val2"]]
   genFunV "projVal" pf (Lf "svar") (Lf "val1")
   runGenV "assignVar" "copyArrVal" [Lf "val2", Lf "arrVal'"]
   genFunV "combineVals" rf (Tup [Lf "val1", Lf "val2"]) (Lf "arrVal'")
   -- create gen function
   setFun out "genConsumers" nt (\_ -> do
     -- create reduce function
     --runGenV "printVar" "printSt" [Lf "svar"]
     addCode ins "consumers" $ decOffVal ++ {-"<copyIdxs>" ++-} "<projVal><copyArrVal><combineVals>" --"<printSt>printVal(\"\\n\");"
     --addCode ins "initStream" $ "<decLens><decStarts><copyLens><copyStarts>"++decBuffer++"<decRootArr><decArr>"++decElems++decLens2++initArr++"<decIdx><decVals>"
     addCode ins "initStream" $ "<decLens><decStarts><copyLens><copyStarts>"++decBuffer++decLens2++"<decIdx><decVals>"
     addCode ins "finStream" ""
     -- get the iterator type name
     --mpTyName <- genTypeName mpty
     --let itTyName = (fromMaybe (error "printAllMap:null map type name!") mpTyName) ++ "::iterator"
     -- declare iterator
     --newVar (Lf "it") intTy
     -- create iterator
     --output "main" $ "<printSt>"
       {-"// visited printAllMap\n" ++
       itTyName ++ " <it>;\n" ++ 
       "for (<it> = <map>.begin(); <it> != <map>.end(); ++<it>) {\n"++
       "  // print it value\n"++
       "  printVal(<it>->first);\n"++
       "  printVal(\" :-> \");\n"++
       "  printVal(<it>->second);\n"++
       "  printVal(\"\\n\");\n"++
       "}\n"-}
     )
t12 t n = terr "groupReduceArrStream" t n

-- |printArrStream template
t11 :: Monad m => Template m
t11 (Lf (LfTy "DistArrStream" [idxTy, valTy, t1, t2, t3, distDims, mirrDims]) :-> t4)
   (LFun _ a             b)
   | match nullFun [t1,t2,t3] && 
     t4 == nullTy &&
     mirrDims == (Lf $ LfTy "MirrDims" []) = do
   -- get input stream vars
   getVar (Lf "svar") a "streamVar"
   getVar (Lf "arrStarts") a "streamIdxStarts"
   getVar (Lf "arrEnds") a "streamIdxEnds"
   getVar (Lf "arrLens") a "streamIdxLens"
   runGenV "assignVar" "copyBounds" [Lf "arrStarts", Lf "arrEnds"]
   -- create gen function
   setFun b "genConsumers" nt (\_ -> do
     runGenV "printVar" "printSt" [Lf "svar"]
     addCode a "consumers" "<copyBounds>\n\n<printSt>printVal(\"\\n\");"
     addCode a "initStream" ""
     addCode a "finStream" ""
     -- get the iterator type name
     --mpTyName <- genTypeName mpty
     --let itTyName = (fromMaybe (error "printAllMap:null map type name!") mpTyName) ++ "::iterator"
     -- declare iterator
     --newVar (Lf "it") intTy
     -- create iterator
     --output "main" $ "<printSt>"
       {-"// visited printAllMap\n" ++
       itTyName ++ " <it>;\n" ++ 
       "for (<it> = <map>.begin(); <it> != <map>.end(); ++<it>) {\n"++
       "  // print it value\n"++
       "  printVal(<it>->first);\n"++
       "  printVal(\" :-> \");\n"++
       "  printVal(<it>->second);\n"++
       "  printVal(\"\\n\");\n"++
       "}\n"-}
     )
t11 t n = terr "printArrStream" t n

-- |printArr template
t13 :: Monad m => Template m
t13 (inTy@(Lf (LfTy "DistArr" [idxTy, valTy, t1, t2, t3, inDims, mirrDims])) :-> t4)
   (LFun _ input             out)
   | match nullFun [t3] && 
     t4 == nullTy &&
     mirrDims == (Lf $ LfTy "MirrDims" []) = do
   -- get input var
   let numInIndices = length $ flattenTree idxTy
   getVar (Lf "arr") input outVarName
   -- iterator var
   newVar (Lf "it") (Lf $ LfTy "IdxIter" [inTy])
   newVar (Lf "itEnd") (Lf $ LfTy "IdxIter" [inTy])
   varExp "arrBegin" "arr" "<v>.beginIndex()" (Lf $ LfTy "IdxIter" [inTy])
   varExp "arrEnd" "arr" "<v>.endIndex()" (Lf $ LfTy "IdxIter" [inTy])
   runGenV "declareVarInit" "decIt" [Lf "it", Lf "arrBegin"]
   runGenV "declareVarInit" "decItEnd" [Lf "itEnd", Lf "arrEnd"]
   varExp "val" "it" "(*<v>.getElement())" valTy
   idxNames <- mapM (\idx -> let n = "idx"++(show idx) in
     do varExp n "it" ("<v>.getIndex()["++(show idx)++"]") intTy ; return $ Lf n) [0..numInIndices-1]
   -- when gen is called, generate assignment
   setFun out "gen" nt (\_ -> do
     runGenV "printVar" "printSt" [Tup [Tup idxNames, Lf "val"]]
     output "main" $ 
       "// print array\n"{-++
       "<decIt><decItEnd>\n"++
       "for (; <it> != <itEnd>; <it>++) { <printSt> }\n"-}
     return ())
t13 t n = terr "printArr" t n




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
module Compiler.Tests.BackEnd1.HistTemplates where

import Compiler.Tests.BackEnd1.NodeLayouts
import Compiler.Tests.BackEnd1.FunSynthesis

import Compiler.Back.Graph
import Compiler.Back.GenDecls
import Compiler.Back.Gen
import Compiler.Back.Generators (genTypeName)
import Compiler.Back.Helper

import Control.Monad.State.Strict (gets)
import Data.Maybe (fromMaybe)

{- genDistRandInts
   readDistList
   reduceDistStream
   mapDistStream
   groupReduceDistStream
   printDistList

   mini
   maxi
   divi
   subi
   addi
-}

-- |nt. shorthand for Nothing.
nt = Nothing

terr :: String -> Ty -> NodeTreeEx -> a
terr tname ty nodes = error $ "Template " ++ tname ++ " error\nType: " ++ (show ty) ++ "\nNodes: " ++ (show nodes) ++ "\n"

templates :: Monad m => [(Id, Template m)]
templates = [
  ("addi", t1),
  ("subi", t2),
  ("divi", t3),
  ("muli", t10),
  ("mini", t4),
  ("maxi", t5),
  ("addf", t16),
  ("subf", t17),
  ("mulf", t18),
  ("divf", t19),
  ("minf", t20),
  ("maxf", t21),
  ("mod", t13),
  ("hash", t28),
  ("floatToInt", t24),
  ("intToFloat", t25),
  ("genDistRandInts", t6),
  ("genDistRandFloats", t23),
  ("readDistVec", t7),
  ("readDistArr1D", t22),
  ("reduceDistStream", t8),
  ("mapDistStream", t9),
  ("printAll", t11),
  ("redistribute", t12),
  ("groupReduceDistStream", t14),
  ("groupReduceDistStreamEx", t27),
  ("readDistMap", t15),
  ("readDistHashMap", t26)
  ]
   
-- |addi template
t1 :: Monad m => Template m
t1 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c)
   | match intTy [t1,t2,t3] = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     --     decName  publicName localName type
     ifnVar "decOut" outVarName (Lf "cv") intTy
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = <av> + <bv>;\n"
       return ())
t1 t n = terr "addi" t n

-- |subi template
t2 :: Monad m => Template m
t2 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c)
   | match intTy [t1,t2,t3] = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "cv") intTy
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = <av> - <bv>;\n"
       return ())
t2 t n = terr "subi" t n

-- |muli template
t10 :: Monad m => Template m
t10 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c) 
   | match intTy [t1,t2,t3] = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "cv") intTy
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = <av> * <bv>;\n"
       return ())
t10 t n = terr "muli" t n

-- |divi template
t3 :: Monad m => Template m
t3 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c)
   | match intTy [t1,t2,t3] = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "cv") intTy
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = <av> / <bv>;\n"
       return ())
t3 t n = terr "divi" t n

-- |mini template
t4 :: Monad m => Template m
t4 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c)
   | match intTy [t1,t2,t3] = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "cv") intTy
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = (<av> < <bv>) ? <av> : <bv>;\n"
       return ())
t4 t n = terr "mini" t n

-- |maxi template
t5 :: Monad m => Template m
t5 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c)
   | match intTy [t1,t2,t3] = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "cv") intTy
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = (<av> < <bv>) ? <bv> : <av>;\n"
       return ())
t5 t n = terr "maxi" t n

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

-- |subf template
t17 :: Monad m => Template m
t17 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c)
   | match floatTy [t1,t2,t3] = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "cv") t3
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = <av> - <bv>;\n"
       return ())
t17 t n = terr "subf" t n

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

-- |divf template
t19 :: Monad m => Template m
t19 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c)
   | match floatTy [t1,t2,t3] = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "cv") t3
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = <av> / <bv>;\n"
       return ())
t19 t n = terr "divf" t n

-- |minf template
t20 :: Monad m => Template m
t20 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c)
   | match floatTy [t1,t2,t3] = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "cv") t3
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = (<av> < <bv>) ? <av> : <bv>;\n"
       return ())
t20 t n = terr "minf" t n

-- |maxf template
t21 :: Monad m => Template m
t21 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c)
   | match floatTy [t1,t2,t3] = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "cv") t3
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = (<av> < <bv>) ? <bv> : <av>;\n"
       return ())
t21 t n = terr "maxf" t n

-- |mod template
t13 :: Monad m => Template m
t13 (Tup [t1, t2] :->  t3)
   (LFun _ (LTup _ [a, b])        c)
      | match intTy [t1,t2,t3] = do
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "cv") intTy
     -- when gen is called, generate assignment
     setFun c "gen" nt (\_ -> do
       output "main" "<decOut><cv> = <av> % <bv>;\n"
       return ())
t13 t n = terr "mod" t n

-- |floatToInt template
t24 :: Monad m => Template m
t24 (t1 :->  t2)
   (LFun _ a  b)
   | t1 == floatTy && t2 == intTy = do
     -- get input vars
     getVar (Lf "av") a outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "bv") t2
     runGenV "genTyName" "targetTy" [Lf "bv"]
     -- when gen is called, generate assignment
     setFun b "gen" nt (\_ -> do
       output "main" "<decOut><bv> = (<targetTy>)<av>;\n"
       return ())
t24 t n = terr "floatToInt" t n

-- |intToFloat template
t25 :: Monad m => Template m
t25 (t1 :->  t2)
   (LFun _ a  b)
   | t1 == intTy && t2 == floatTy = do
     -- get input vars
     getVar (Lf "av") a outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "bv") t2
     runGenV "genTyName" "targetTy" [Lf "bv"]
     -- when gen is called, generate assignment
     setFun b "gen" nt (\_ -> do
       output "main" "<decOut><bv> = (<targetTy>)<av>;\n"
       return ())
t25 t n = terr "floatToInt" t n

-- |hash template
-- |TODO add <type>Hasher variables to struct declarations.
t28 :: Monad m => Template m
t28 (t1 :->  t2)
   (LFun _ a  b)
   | t2 == intTy = do
     -- get input vars
     getVar (Lf "av") a outVarName
     -- create output var if doesn't already exist
     ifnVar "decOut" outVarName (Lf "bv") intTy
     runGenV "genTyName" "srcTy" [Lf "av"]
     -- when gen is called, generate assignment
     setFun b "gen" nt (\_ -> do
       output "main" "<decOut><bv> = <srcTy>Hasher(<av>);\n"
       return ())
t28 t n = terr "hash" t n

-- |genDistRandInts template
t6 :: Monad m => Template m
t6 (inTy :->   
    outT@(Lf (LfTy "DistVec" [Tup [t1, t2], _, _, nodeSet]))) 
   (LFun _ numInts distVec) 
   | match intTy [inTy,t1,t2]= do
     -- get var for current nodeset (lookup using dist type)
     getNodeSetVar "ns" nodeSet
     varExp "numNodes" "ns" "<v>.partitionCount" intTy
     varExp "nodeIdx" "ns" "<v>.partitionRank" intTy
     -- get input var
     getVar (Lf "n") numInts outVarName
     -- create intermediate vars
     newVar (Lf "startI") intTy
     newVar (Lf "localN") intTy
     newStructVar (Lf "s") (Tup [intTy, intTy])
     aliasVar (Tup [Lf "i", Lf "v"]) (Lf "s")
     -- create output var if doesn't already exist
     ifnVar "decVec" outVarName (Lf "l") outT
     -- when gen is called, generate assignment
     setFun distVec "gen" nt (\_ -> do
       --runGenV "declareVar" "decVec" [Lf "l"]
       runGenV "declareVar" "decVar" [Lf "s"]
       output "main" $
         -- declare list and it vars
         "// genDistRandInts: \n"++
         "<decVec>"++
         "<decVar>"++
         -- calculate how many nums to make locally
         -- and start value of i for this node
         "int <startI> = <n> % <numNodes>;\n"++ -- number of "extra 1's"
         "int <localN> = <n> / <numNodes>;\n"++ -- size of parts before "extra 1's"
         "if (<nodeIdx> < <startI>) {\n" ++ -- are we before the end of "extra 1's"?
         "  <startI> = (<nodeIdx> * <localN>) + <nodeIdx>;\n"++
         "  <localN>++;\n"++ -- include an extra 1 in this part
         "} else {\n"++ -- we are after the end of "extra 1's", so don't need to add one to localN
         "  <startI> += <nodeIdx> * <localN>;\n"++ -- numExtraOnes + normalStartIdx. note: the PLUS equals
         "}\n"++
         -- allocate capacity for them
         "<l>.reserve(<localN>);\n"++
         -- create the random numbers
         "for (<i> = <startI>; <i> < (<startI> + <localN>); <i>++) {\n" ++ 
         "  <v> = rand();\n" ++
         "  <l>.push_back(<s>);\n"++
         "}\n\n"
       return ())
t6 t n = terr "genDistRandInts" t n

-- |genDistRandFloats template
t23 :: Monad m => Template m
t23 (inTy :->   
    outT@(Lf (LfTy "DistArr1D" [t1, _, _, nodeSet]))) 
   (LFun _ numFloats distVec) 
   | intTy == inTy && floatTy == t1 = do
     -- get var for current nodeset (lookup using dist type)
     getNodeSetVar "ns" nodeSet
     varExp "numNodes" "ns" "<v>.partitionCount" intTy
     varExp "nodeIdx" "ns" "<v>.partitionRank" intTy
     -- get input var
     getVar (Lf "n") numFloats outVarName
     -- create intermediate vars
     newVar (Lf "startI") intTy
     newVar (Lf "localN") intTy
     newVar (Lf "s") floatTy
     newVar (Lf "i") intTy
     -- create output var if doesn't already exist
     ifnVar "decVec" outVarName (Lf "l") outT
     -- when gen is called, generate assignment
     setFun distVec "gen" nt (\_ -> do
       runGenV "declareVar" "decVar" [Lf "s"]
       runGenV "declareVar" "decIdx" [Lf "i"]
       output "main" $
         -- declare list and it vars
         "// genDistRandFloats: \n"++
         "<decVec>"++
         "<decVar>"++
         "<decIdx>"++
         -- calculate how many nums to make locally
         -- and start value of i for this node
         "int <startI> = <n> % <numNodes>;\n"++ -- number of "extra 1's"
         "int <localN> = <n> / <numNodes>;\n"++ -- size of parts before "extra 1's"
         "if (<nodeIdx> < <startI>) {\n" ++ -- are we before the end of "extra 1's"?
         "  <startI> = (<nodeIdx> * <localN>) + <nodeIdx>;\n"++
         "  <localN>++;\n"++ -- include an extra 1 in this part
         "} else {\n"++ -- we are after the end of "extra 1's", so don't need to add one to localN
         "  <startI> += <nodeIdx> * <localN>;\n"++ -- numExtraOnes + normalStartIdx. note: the PLUS equals
         "}\n"++
         -- allocate capacity for them
         "<l>.reserve(<localN>);\n"++
         -- create the random numbers
         "for (<i> = <startI>; <i> < (<startI> + <localN>); <i>++) {\n" ++ 
         "  <s> = randFloat();\n" ++
         "  <l>.push_back(<s>);\n"++
         "}\n\n"
       return ())
t23 t n = terr "genDistRandFloats" t n

-- |readDistVec template
t7 :: Monad m => Template m
t7 (inTy@(Lf (LfTy "DistVec" [et, _, _, nlIn])) :->  
          Lf (LfTy "DistStm" [_, _, _, nlOut])) 
   (LFun _ distVec                          distStm) = do
     -- get nodeset var
     assertM (return $ nlIn == nlOut) "readDistVec: node layouts don't match"
     getNodeSetVar "nl" nlIn
     -- get input var
     getVar (Lf "v") distVec outVarName
     -- create iterator var
     newVar (Lf "it") (Lf $ LfTy "Iter" [inTy])
     runGenV "declareVar" "decIt" [Lf "it"]
     -- create output stream var
     varExp "sv" "it" "(*<v>)" et
     setVar distStm "streamVar" (Lf "sv")
     -- when gen is called, generate assignment
     setFun distStm "gen" nt (\_ -> do
       -- generate stream consumer code blocks
       genTrace "entered readDistVec.gen"
       callAll distStm "genConsumers" nt
       getCode "init" distStm "initStream"
       getCode "fin" distStm "finStream"
       getCode "consume" distStm "consumers"
       -- only perform if this node is in the node layout, and is one 
       -- of the root nodes (rather than a mirror node)
       output "main" "// readDistVec\n"
       output "main" $ 
         "<init> // init readDistVec\n"++
         "if (NL_ON_FRINGE(<nl>)) {\n"++
         "  <decIt> // declare readDistVec iterator\n"++
         "  for (<it> = <v>.begin(); <it> != <v>.end(); ++<it>) {\n"++
         "  // begin readDistVec consume\n"++
         "  <consume>\n"++
         "  // end readDistVec consume\n"++
         "  }\n"++
         "}\n"++
         "<fin> // finish readDistVec\n\n"
       return ())
t7 t n = terr "readDistVec" t n

-- |readDistArr1D template
t22 :: Monad m => Template m
t22 (inTy@(Lf (LfTy "DistArr1D" [et, _, _, nlIn])) :->  
           Lf (LfTy "DistStm" [Tup [ity, et2], _, _, nlOut])) 
   (LFun _ distVec                          distStm) 
   | et == et2 && ity == intTy = do
     -- get nodeset var
     assertM (return $ nlIn == nlOut) "readDistVec: node layouts don't match"
     getNodeSetVar "nl" nlIn
     varExp "nodeIdx" "nl" "<v>.partitionRank" intTy
     -- get input var
     getVar (Lf "v") distVec outVarName
     -- create iterator var
     newVar (Lf "it") (Lf $ LfTy "Iter" [inTy])
     runGenV "declareVar" "decIt" [Lf "it"]
     -- create index var
     newVar (Lf "idx") intTy
     runGenV "declareVar" "decIdx" [Lf "idx"]
     -- create output stream var
     varExp "sv" "it" "(*<v>)" et
     setVar distStm "streamVar" (Tup [Lf "idx", Lf "sv"])
     -- when gen is called, generate assignment
     setFun distStm "gen" nt (\_ -> do
       -- generate stream consumer code blocks
       genTrace "entered readDistVec.gen"
       callAll distStm "genConsumers" nt
       getCode "init" distStm "initStream"
       getCode "fin" distStm "finStream"
       getCode "consume" distStm "consumers"
       -- only perform if this node is in the node layout, and is one 
       -- of the root nodes (rather than a mirror node)
       output "main" "// readDistArr1D\n"
       output "main" $ 
         "// readDistArr1D:init\n"++
         "<init>\n "++
         "if (NL_ON_FRINGE(<nl>)) {\n"++
         "  // calc start index for this node\n"++
         "  <decIdx> // declare readDistArr1D index\n"++
         "  // TODO THIS IS BROKEN, NEEDS TO PASS OFFSET AROUND WITH VECTOR \n"++
         "  // BECAUSE SOMETIMES VECTOR WON'T DIVIDE EVENLY\n"++
         "  <idx> = <nodeIdx> * <v>.size();\n"++
         "  <decIt> // declare readDistArr1D iterator\n"++
         "  for (<it> = <v>.begin(); <it> != <v>.end(); ++<it>) {\n"++
         "  // begin readDistVec consume\n"++
         "  <consume>\n"++
         "  // end readDistVec consume\n"++
         "  <idx>++; // next index\n"++
         "  }\n"++
         "}\n"++
         "<fin> // finish readDistArr1D\n\n"
       return ())
t22 t n = terr "readDistArr1D" t n

-- TODO Is it safe to just assume we can do this at every
--   node that the stream is being read on? Are there situations
--   where the reader's node layout is different to the stream consumers?
--   (THIS MUST NEVER BE PERMITTED TO HAPPEN) 
-- |reduceDistStream template
t8 :: Monad m => Template m
t8 (Tup [et :-> st,         -- proj fun
         Tup [st1, st2] :-> st3, -- bin fun
         Lf (LfTy "DistStm" [et2, _, _, nl])] :-> rt)
   (LFun _ (LTup _ [projf, binf, ins])    out) 
   | et == et2 && match st [st1, st2, st3, rt] = do
     -- get node layout var
     getNodeSetVar "nl" nl
     -- get stream var
     getVar (Lf "sv") ins "streamVar"
     genTrace "reduceDistStream:gotStreamVar"
     -- create intermediate vars
     newVar (Lf "val1") rt
     newVar (Lf "val2") rt
     genTrace "reduceDistStream:madeNewVars val1 and val2"
     -- create output vars
     newStructVar (Lf "res") rt
     newStructVar (Lf "inres") rt
     setVar out outVarName (Lf "res") 
     genTrace "reduceDistStream:created out vars"
     -- declare AllReduce Op
     combineFun <- getFun binf
     genTrace "reduceDistStream:got combineFun"
     runGen "reduceFun" "redFunName" [TyV et, combineFun]
     genTrace "reduceDistStream:generated reduceFun"
     newVar (Lf "redOp") intTy
     output "decls" "MPI::Op <redOp>;\n\n"
     output "init" "<redOp>.Init(&<redFunName>, true);\n\n"
     -- def "genConsumers" to generate print statements
     setFun out "genConsumers" nt (\_ -> do
       genTrace "entered reduceDistStream.genConsumers"
       -- declare output var
       runGenV "declareVar" "decOut" [Lf "res"]
       -- declare vars
       runGenV "declareVar" "decVal1" [Lf "val1"]
       runGenV "declareVar" "decVal2" [Lf "val2"]
       runGenV "declareVar" "decRes" [Lf "res"]
       genTrace "reduceDistStream:generated var decls"
       -- generate code to get new key and new val
       genFunV "projVal" projf (Lf "sv") (Lf "val1")
       genFunV "combineVals" binf (Tup [Lf "res", Lf "val1"]) (Lf "val2")
       runGenV "assignVar" "copyRes" [Lf "res", Lf "val2"]
       genTrace "reduceDistStream:generated projf, binf, and copyRes"
       -- init: declare result
       addCode ins "initStream" "// reduceDistStream:initStream\n<decOut>"
       genTrace "reduceDistStream:added out decl to initStream"
       -- consume: reduce 
       addCode ins "consumers" $ 
         "// reduceDistStream:consumers \n"++
         "// decVal1\n<decVal1>\n"++
         "// decVal2\n<decVal2>\n"++
         "// projVal\n<projVal>\n"++
         "// combineVals\n<combineVals>\n"++
         "// copyRes\n<copyRes>\n"
       genTrace "reduceDistStream:added to consumers"
       -- final: allreduce, then broadcast
       runGenV "declareVar" "decOut2" [Lf "inres"]
       runGenV "assignVar" "copyRes2" [Lf "inres", Lf "res"]
       resTyNameMb <- genTypeName et
       let resTyName = fromMaybe (error $ "reduceDistStream: can't get result type name!") resTyNameMb
       setLocalVal "resTyName" $ IdV resTyName
       addCode ins "finStream" $ 
         "// reduceDistStream:finStream\n"++ 
         -- if node layout is COMM_WORLD, do an AllReduce
         (if nl == allNodesTy then
         "// allreduce among all nodes\n"++
         "<decOut2><copyRes2>\n"++
         "<nl>.partitionCom->Allreduce(&<inres>, &<res>, sizeof(<resTyName>), MPI_PACKED, <redOp>);\n"
         -- if some other layout, Reduce and then Broadcast to all
         else 
         "// reduce to one node\n"++
         "if (NL_ON_FRINGE(<nl>)) {\n"++
         "  <decOut2><copyRes2>\n"++
         "  <nl>.partitionCom->Reduce(&<inres>, &<res>, sizeof(<resTyName>), MPI_PACKED, <redOp>, 0);\n"++
         "}\n"++
         "// broadcast to all other nodes\n"++ 
         "int destRank;\n"++
         "translateRank(<nl>.partitionCom, 0, allNodes.partitionCom, &destRank);\n"++
         "allNodes.partitionCom->Bcast(&<res>, sizeof(<resTyName>), MPI_PACKED, destRank);\n")
       genTrace "reduceDistStream:added to finStream"
       )
t8 t n = terr "reduceDistStream" t n

-- mapDistStream template
t9 :: Monad m => Template m 
t9 (Tup [k1t :-> k2t, 
         Tup [k1t2, v1t] :-> v2t,
         Lf (LfTy "DistStm" [Tup [k1t3, v1t2], _, _, nl1])] :-> 
         Lf (LfTy "DistStm" [Tup [k2t2, v2t2], _, _, nl2]))
   (LFun _ (LTup _ [kf, vf, a])                        b) 
   | match k1t [k1t2, k1t3] && v1t == v1t2 && k2t == k2t2 && v2t == v2t2 = do
   -- sanity check
   assertM (return $ nl1 == nl2) "mapDistStream: node layouts don't match"
   -- get producer's stream var
   getVar (Tup [Lf "inKey", Lf "inVal"]) a "streamVar"
   -- create consumer stream var
   newVar (Tup [Lf "outKey", Lf "outVal"]) (Tup [k2t, v2t])
   -- set stream var for b
   setVar b "streamVar" (Tup [Lf "outKey", Lf "outVal"])
   -- def "genConsumers" to generate consumers
   setFun b "genConsumers" nt (\_ -> do
     genTrace "entered mapDistStream.genConsumers"
     -- generate outs declaration
     runGenV "declareVar" "decOuts" [Tup [Lf "outKey", Lf "outVal"]]
     -- generate key fun implementation
     genFunV "kfCode" kf (Lf "inKey") (Lf "outKey")
     genFunV "vfCode" vf (Tup [Lf "inKey", Lf "inVal"]) (Lf "outVal")
     -- generate b's consumers
     --setCode b "consumers" "" -- init to empty
     callAll b "genConsumers" nt
     getCode "consume" b "consumers"
     getCode "init" b "initStream"
     getCode "fin" b "finStream"
     -- add these consumers to parent
     addCode a "consumers" "// mapDistStream:\n//decOuts\n<decOuts>//kfCode\n<kfCode>//vfCode\n<vfCode>\n//consume:\n<consume>\n"
     addCode a "initStream" "<init>"
     addCode a "finStream" "<fin>"
     )
   return ()
t9 t n = terr "mapDistStream" t n

-- |printAllMap template
t11 :: Monad m => Template m
t11 (Lf (LfTy "DistStm" [elTy, t1, t2, nl]) :-> t3)
   (LFun _ a             b)
   | match nullTy [t1,t2,t3] = do
   -- get input var
   getVar (Lf "svar") a "streamVar"
   -- create gen function
   setFun b "genConsumers" nt (\_ -> do
     runGenV "printVar" "printSt" [Lf "svar"]
     addCode a "consumers" "<printSt>printVal(\"\\n\");"
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
t11 t n = terr "printAll" t n

-- |redistribute template
t12 :: Monad m => Template m
t12 (inTy@(Lf (LfTy "DistStm" [elTy, t1, t2, inNl])) :->
     outT@(Lf (LfTy "DistVec" [_   , outKf, outPf, outNl])))
   (LFun _ a             b)
   | match nullTy [t1,t2] = do
   -- get node layout vars
   getNodeSetVar "inNl" inNl
   getNodeSetVar "outNl" outNl
   -- get type name of elTy, so can do sizeof
   elTyNameMb <- genTypeName elTy
   let elTyName = fromMaybe (error $ "reduceDistStream: can't get result type name!") elTyNameMb
   setLocalVal "elTyName" $ IdV elTyName
   -- get input var
   getVar (Lf "svar") a "streamVar"
   -- create result var
   ifnVar "decVec" outVarName (Lf "outV") outT
   -- create intermediate vars
   newStructVar (Lf "el") elTy -- copy of element
   varExp "pcount" "outNl" "<v>.partitionCount" intTy
   newVar (Lf "pid") intTy -- current partition id
   newVar (Lf "sendBuffs") outT -- array of vectors, one for each part
   newVar (Lf "sendCnts") intTy -- sizes in bytes of each send partition
   newVar (Lf "recvCnts") intTy -- sizes in bytes of each recv partition
   newVar (Lf "sendDispls") intTy -- addresses of sendBuffers
   newVar (Lf "recvDispls") intTy -- displacements in recvBuff to put each received part
   newVar (Lf "recvTotal") intTy -- total number of elements in the local recvBuff
   -- declare vars
   runGenV "declareVar" "decCons" [Tup [Lf "pid", Lf "el"]]
   runGenV "declareVar" "decTotal" [Lf "recvTotal"]
   runGenV "declareArr" "decBuff" [Lf "sendBuffs", Lf "pcount"]
   runGenV "declareArr" "decArrs" [Tup [Lf "sendCnts", Lf "recvCnts",
     Lf "sendDispls", Lf "recvDispls"], Lf "pcount"]
   -- gen code
   runGenV "assignVar" "copyEl" [Lf "el", Lf "svar"] -- pack element in struct
   -- work out partition it belongs in
   genFunsFromTy "outPf" outKf outPf (Lf "svar") (Lf "pid")
   -- create gen function
   setFun b "genConsumers" nt (\_ -> do
     addCode a "consumers" "<decCons><copyEl><outPf>\n<sendBuffs>[<pid>].push_back(<el>);"
     addCode a "initStream" "<decBuff>"
     addCode a "finStream" $ 
       "<decArrs>"++
       "// send/recv partition sizes\n"++
       "for (int <pid> = 0; <pid> < <pcount>; <pid>++) {\n"++
       "  <sendCnts>[<pid>] = <sendBuffs>[<pid>].size() * sizeof(<elTyName>);  // sendCnts\n"++
       "  <sendDispls>[<pid>] = MPI::Get_address(&<sendBuffs>[<pid>].front()); // sendDispls\n"++
       "}\n"++
       "<outNl>.partitionCom->Alltoall(<sendCnts>, 1, MPI_INT, <recvCnts>, 1, MPI_INT);\n"++
       "// sum counts, and make displacements\n"++
       "<decTotal>\n"++
       "for (int <pid> = 0; <pid> < <pcount>; <pid>++) {\n"++
       "  <recvDispls>[<pid>] = <recvTotal>; // recv displs\n"++
       "  <recvTotal> += <recvCnts>[<pid>]; // total bytes to recv\n"++
       "}\n"++
       "<recvTotal> /= sizeof(<elTyName>); // total elements to recv\n"++
       "// allocate vector to receive in\n"++
       "<decVec>\n"++
       --"<outV>.reserve(<recvTotal>); // reserve room for total elements\n"++
       "<outV>.resize(<recvTotal>); // reserve room for total elements\n"++
       "// send/recv partitions\n"++
       "<outNl>.partitionCom->Alltoallv(MPI_BOTTOM, <sendCnts>, <sendDispls>, MPI_PACKED,\n"++
       "    &<outV>.front(), <recvCnts>, <recvDispls>, MPI_PACKED);\n"
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
t12 t n = terr "redistribute" t n

-- |groupReduceDistStream template
t14 :: Monad m => Template m
t14 (Tup [Tup [k1t, v1t] :-> k2t,
         Tup [_, _] :-> v2t,
         Tup [_, _] :-> _, 
         inTy@(Lf (LfTy "DistStm" [elTy, t1, t2, inNl]))] :-> 
         outT@(Lf (LfTy "DistMap" [_, _, outKf, outPf, outNl])))
   (LFun _ (LTup _ [kf, vf, rf, s])    m) 
   | match nullTy [t1,t2] = do
     -- sanity check
     assertM (return $ inNl == outNl) "groupReduceDistStream: node layouts don't match"
     -- create new key and new val vars
     newStructVar (Lf "key2") k2t
     newVar (Lf "val2") v2t
     newStructVar (Lf "val3") v2t
     newStructVar (Lf "val4") v2t
     -- create output Map var
     ifnVar "decOutMap" outVarName (Lf "outMap") outT
     -- create iterator var
     newVar (Lf "it") (Lf $ LfTy "Iter" [outT])
     -- get stream var
     getVar (Tup [Lf "key1", Lf "val1"]) s "streamVar"
     -- def "genConsumers" to generate print statements
     setFun m "genConsumers" nt (\_ -> do
       curNid <- gets genCurrentNode
       genTrace $ "entered groupReduceDistStream.genConsumers: " ++ (show curNid) ++ "\n"
       -- declare vars
       runGenV "declareVar" "decIt" [Lf "it"]
       runGenV "declareVar" "decKey2" [Lf "key2"]
       runGenV "declareVar" "decVal2" [Lf "val2"]
       runGenV "declareVar" "decVal3" [Lf "val3"]
       runGenV "declareVar" "decVal4" [Lf "val4"]
       k2 <- getLocalVal "key2"
       -- generate code to get new key and new val
       genFunV "genNewKey" kf (Tup [Lf "key1", Lf "val1"]) (Lf "key2")
       genFunV "genNewVal" vf (Tup [Lf "key1", Lf "val1"]) (Lf "val2")
       genFunV "combineVals" rf (Tup [Lf "val2", Lf "val3"]) (Lf "val4")
       -- add init and append statement to consumers
       addCode s "initStream" "<decOutMap>"
       addCode s "consumers" $ 
         "//begin groupReduceStrmMap consumer\n"++
         "<decKey2>\n"++
         "<decVal2>\n"++
         "<decVal3>\n"++
         "<decVal4>\n"++
         "<decIt>\n"++
         --"// key2: " ++ (show k2) ++ "\n"++
         "<genNewKey>\n"++
         "<genNewVal>\n"++
         "<it> = <outMap>.find(<key2>);\n"++
         "if (<it> == <outMap>.end()) {\n"++ 
         "  <outMap>[<key2>] = <val2>;\n"++
         "} else {\n"++
         "  <val3> = <outMap>[<key2>];\n"++
         "  <combineVals>\n"++
         "  <outMap>[<key2>] = <val4>;\n"++ -- TODO MORE EFFICIENT UPDATE???
         "}\n"++
         "//end groupReduceStrmMap consumer\n"
       addCode s "finStream" ""
       )
t14 t n = terr "groupReduceDistStream" t n

-- |groupReduceDistStreamEx template
t27 :: Monad m => Template m
t27 (Tup [Tup [k1t, v1t] :-> k2t,
         Tup [k1t2, v1t2] :-> v2t,
         Tup [v2t2, v2t3] :-> v2t4, 
         inTy@(Lf (LfTy "DistStm" [Tup [k1t3, v1t3], t1, t2, inNl]))] :-> 
         outT@(Lf (LfTy "DistHashMap" [k2t2, v2t5, outKf, outPf, outNl])))
   (LFun _ (LTup _ [kf, vf, rf, s])    m) 
   | match nullTy [t1,t2] && match k1t [k1t2, k1t3] && 
     match v1t [v1t2, v1t3] && k2t == k2t2 && match v2t [v2t2, v2t3, v2t4, v2t5] = do
     -- get node sets
     assertM (return $ inNl == outNl) "groupReduceDistStreamEx: node layouts don't match. must be same for alltoallv to work."
     getNodeSetVar "inNl" inNl
     getNodeSetVar "outNl" outNl
     -- create new key and new val vars
     newStructVar (Lf "key2") k2t
     runGenV "genTyName" "keyTyName" [Lf "key2"]
     newVar (Lf "val2") v2t
     newStructVar (Lf "val3") v2t
     newStructVar (Lf "val4") v2t
     -- create output Map var
     ifnVar "decOutMap" outVarName (Lf "outMap") outT
     -- create iterator var
     newVar (Lf "it") (Lf $ LfTy "Iter" [outT])
     runGenV "declareVar" "decIt" [Lf "it"]
     varExp "itKey" "it" "(<v>->first)" k2t
     varExp "itVal" "it" "(<v>->second)" v2t
     -- get stream var
     getVar (Tup [Lf "key1", Lf "val1"]) s "streamVar"

     -- vars for repartitioning
     let elTy = Tup [k2t, v2t]
     genTrace $ "elTy: " ++ show elTy
     newStructVar (Lf "el") elTy -- copy of element
     runGenV "genTyName" "elTy" [Lf "el"]
     varExp "pcount" "outNl" "<v>.partitionCount" intTy
     newVar (Lf "pid") intTy -- current partition id
     let vecTy = Lf $ (LfTy "DistVec" [elTy, outKf, outPf, outNl])
     runGenV "declareVar" "decCons" [Tup [Lf "pid", Lf "el"]]
     newVar (Lf "sendBuffs") outT -- array of vectors, one for each part
     --newVar (Lf "sendCnts") intTy -- sizes in bytes of each send partition
     newVar (Lf "sendBuffs") vecTy -- array of vectors, one for each part
     runGenV "declareArr" "decBuff" [Lf "sendBuffs", Lf "pcount"]
     -- pack pair in struct
     runGenV "assignVar" "copyEl" [Lf "el", Tup [Lf "itKey", Lf "itVal"]]
     -- work out partition it belongs in
     genFunsFromTy "outPf" outKf outPf (Lf "el") (Lf "pid")

     -- vars for reading partitions into hashmap
     let vecTy = Lf (LfTy "DistVec" [elTy, outKf, outPf, outNl])
     newVar (Lf "recvBuff") vecTy
     runGenV "declareVar" "decRecvBuff" [Lf "recvBuff"]
     newVar (Lf "vit") (Lf $ LfTy "Iter" [vecTy])
     varExp "vitEl" "vit" "(*<v>)" elTy
     runGenV "declareVar" "decVIt" [Lf "vit"]
     runGenV "assignVar" "copyEl2" [Tup [Lf "key2", Lf "val2"], Lf "vitEl"]

     -- def "genConsumers" to generate print statements
     setFun m "genConsumers" nt (\_ -> do
       curNid <- gets genCurrentNode
       genTrace $ "entered groupReduceDistStreamEx.genConsumers: " ++ (show curNid) ++ "\n"
       -- declare vars
       runGenV "declareVar" "decKey2" [Lf "key2"]
       runGenV "declareVar" "decVal2" [Lf "val2"]
       runGenV "declareVar" "decVal3" [Lf "val3"]
       runGenV "declareVar" "decVal4" [Lf "val4"]
       k2 <- getLocalVal "key2"
       -- generate code to get new key and new val
       genFunV "genNewKey" kf (Tup [Lf "key1", Lf "val1"]) (Lf "key2")
       genFunV "genNewVal" vf (Tup [Lf "key1", Lf "val1"]) (Lf "val2")
       genFunV "combineVals" rf (Tup [Lf "val2", Lf "val3"]) (Lf "val4")
       -- create hashmap declaration
       addCode s "initStream" $ 
         "// declare hashmap\n <decOutMap> // TODO init size\n" ++ 
         "<outMap>.set_empty_key(<keyTyName>Empty);\n"
       -- create populate hashmap consumer
       addCode s "consumers" $ 
         "//begin groupReduceDistStreamEx consumer\n"++
         "<decKey2>\n"++
         "<decVal2>\n"++
         "<decVal3>\n"++
         "<decVal4>\n"++
         -- TODO try pointers to vals as well as vals
         -- TODO more efficient update (add inline "update" that takes a function)
         "<genNewKey>\n"++
         "<genNewVal>\n"++
         "if (<outMap>.count(<key2>)) {\n"++ 
         "  <val3> = <outMap>[<key2>];\n"++
         "  <combineVals>\n"++
         "  <outMap>[<key2>] = <val4>;\n"++
         "} else {\n"++
         "  <outMap>[<key2>] = <val2>;\n"++
         "}\n"++
         "//end groupReduceDistStreamEx consumer\n" 
       -- create hashmap distribution code
       addCode s "finStream" $ 
         "// groupReduceDistStreamEx read into partition vectors\n"++
         "<decBuff>\n<decIt>\n"++
         "for (<it> = <outMap>.begin(); <it> != <outMap>.end(); ++<it>) {\n"++
         "  <decCons><copyEl><outPf>\n<sendBuffs>[<pid>].push_back(<el>);\n"++
         "}\n"++
         "// redistribute local hash maps\n"++
         "<decRecvBuff>\n"++
         "exchangePartitions<<elTy> >(<sendBuffs>, &<recvBuff>, &<inNl>);\n"++
         "// read from recv buffs into local hash map\n"++
         "<outMap>.clear_no_resize();\n"++
         "<decVIt>\n"++
         "<decKey2>\n"++
         "<decVal2>\n"++
         "<decVal3>\n"++
         "<decVal4>\n"++
         "for (<vit>=<recvBuff>.begin(); <vit>!=<recvBuff>.end(); <vit>++) {\n"++
         "  <copyEl2>\n"++
         "  if (<outMap>.count(<key2>)) {\n"++ 
         "    <val3> = <outMap>[<key2>];\n"++
         "    <combineVals>\n"++
         "    <outMap>[<key2>] = <val4>;\n"++
         "  } else {\n"++
         "    <outMap>[<key2>] = <val2>;\n"++
         "  }\n"++
         "}\n"
       )
t27 t n = terr "groupReduceDistStreamEx" t n 

-- |readDistMap template
t15 :: Monad m => Template m
t15 (inTy@(Lf (LfTy "DistMap" [kt, vt, _, _, nlIn])) :->  
           Lf (LfTy "DistStm" [_, _, _, nlOut])) 
   (LFun _ distMap distStm) = do
     -- get nodeset var
     assertM (return $ nlIn == nlOut) "readDistMap: node layouts don't match"
     getNodeSetVar "nl" nlIn
     -- get input var
     getVar (Lf "v") distMap outVarName
     -- create iterator var
     newVar (Lf "it") (Lf $ LfTy "Iter" [inTy])
     runGenV "declareVar" "decIt" [Lf "it"]
     -- create output stream var
     varExp "ksv" "it" "<v>->first" kt
     varExp "vsv" "it" "<v>->second" vt
     setVar distStm "streamVar" (Tup [Lf "ksv", Lf "vsv"])
     -- when gen is called, generate assignment
     setFun distStm "gen" nt (\_ -> do
       -- generate stream consumer code blocks
       genTrace "entered readDistMap.gen"
       callAll distStm "genConsumers" nt
       getCode "init" distStm "initStream"
       getCode "fin" distStm "finStream"
       getCode "consume" distStm "consumers"
       -- only perform if this node is in the node layout, and is one 
       -- of the root nodes (rather than a mirror node)
       output "main" "// readDistMap\n"
       output "main" $ 
         "<init>\n"++
         "if (NL_ON_FRINGE(<nl>)) {\n"++
         "  <decIt>"++
         "  for (<it> = <v>.begin(); <it> != <v>.end(); ++<it>) {\n"++
         "  <consume>\n"++
         "  }\n"++
         "}\n"++
         "<fin>\n\n"
       return ())
t15 t n = terr "readDistMap" t n

-- |readDistHashMap template
t26 :: Monad m => Template m
t26 (inTy@(Lf (LfTy "DistHashMap" [kt, vt, _, _, nlIn])) :->  
           Lf (LfTy "DistStm" [Tup [kt', vt'], _, _, nlOut])) 
   (LFun _ distMap distStm) 
   | kt == kt' && vt == vt' = do
     -- get nodeset var
     assertM (return $ nlIn == nlOut) "readDistHashMap: node layouts don't match"
     getNodeSetVar "nl" nlIn
     -- get input var
     getVar (Lf "v") distMap outVarName
     -- create iterator var
     newVar (Lf "it") (Lf $ LfTy "Iter" [inTy])
     runGenV "declareVar" "decIt" [Lf "it"]
     -- create output stream var
     varExp "ksv" "it" "<v>->first" kt
     varExp "vsv" "it" "<v>->second" vt
     setVar distStm "streamVar" (Tup [Lf "ksv", Lf "vsv"])
     -- when gen is called, generate assignment
     setFun distStm "gen" nt (\_ -> do
       -- generate stream consumer code blocks
       genTrace "entered readDistHashMap.gen"
       callAll distStm "genConsumers" nt
       getCode "init" distStm "initStream"
       getCode "fin" distStm "finStream"
       getCode "consume" distStm "consumers"
       -- only perform if this node is in the node layout, and is one 
       -- of the root nodes (rather than a mirror node)
       output "main" "// readDistHashMap\n"
       output "main" $ 
         "<init>\n"++
         "if (NL_ON_FRINGE(<nl>)) {\n"++
         "  <decIt>"++
         "  for (<it> = <v>.begin(); <it> != <v>.end(); ++<it>) {\n"++
         "  <consume>\n"++
         "  }\n"++
         "}\n"++
         "<fin>\n\n"
       return ())
t26 t n = terr "readDistHashMap" t n

--LfTy "Array" [eTy, Lf $ LfTy "nl1.partitionCount" []]

-- TODO How to deal with Mirroring and scalar functions?
-- Perhaps just a datatype with no Mirr, is mirrored?

-- TODO 
-- info about Distribution layout:
--   - am i part of this nodeset fringe?
--   - how many are in this nodeset fringe?
--   - what rank am i in this nodeset fringe?

-- TODO add  types for lists &/ distributed stuff...



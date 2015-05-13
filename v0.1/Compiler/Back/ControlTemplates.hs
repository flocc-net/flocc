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
module Compiler.Back.ControlTemplates (ctrlTemplates) where

import qualified Data.Map as DM
import Control.Monad.State.Strict (gets)

import Compiler.Back.Graph
import Compiler.Back.GenDecls
import Compiler.Back.Gen
import Compiler.Back.Helper
import Compiler.Back.Templates

import Control.Monad.Catch

ctrlTemplates :: (Monad m, MonadCatch m) => [(Id, Template m)]
ctrlTemplates = [
    ("ifFun", ifT),
    ("loop", t01)
  ]

-- |ifFun template (for conditionals)
ifT :: (Monad m, MonadCatch m) => Template m
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
      genFunV "thenCode" thenN (Lf "nullV") n0 (Lf "res")
      genFunV "elseCode" elseN (Lf "nullV") n0 (Lf "res")
      outputDecl thisN "<decOut>"
      -- gen if block
      setFun thisN "gen" nt (\_ -> do
     --  outputDecl thisN "<decOut>"
       output "main" $ 
         "// begin <tem>\n" ++
         "if (<predV>) {\n<thenCode>\n} else {\n<elseCode>\n}\n"++
         "// end <tem>\n"
       return ())
ifT t n = terr' t n

-- |while template
-- |TODO copy public members from output of nextf to input of nextf?
t01 :: (Monad m, MonadCatch m) => Template m
t01 (Tup [st1 :-> st2, st3 :-> boolTy, st4] :-> st5)
   (LFun _ (LTup _ [nextf, predf, v0])            out)
   | match (ignoreFunsTy st1) (map ignoreFunsTy [st2, st3, st4, st5]) = do
     -- get init val
     getVar (Lf "v0") v0 outVarName
     -- TODO get everything in v0's public environment other than the outVar and streamVar 
     --      and pass it to genFunV calls
     -- buffer vars
     -- newVar (Lf "v1") st1 -- 
     ifnVar "decOut" outVarName (Lf "v1") st1
     newVar (Lf "v2") st1
     --runGenV "declareVar" "decBuffs" [Tup [Lf "v1", Lf "v2"]]
     runGenV "declareVar" "decBuffs" [Lf "v2"]
     genFunV "appNext0" nextf (Lf "v0") v0 (Lf "v1")
     genFunV "appNext1" nextf (Lf "v1") v0 (Lf "v2")
     genFunV "appNext2" nextf (Lf "v2") v0 (Lf "v1")
     runGenV "assignVar" "copyBuff" [Lf "v1", Lf "v2"] 
     runGenV "assignVar" "copyBuff2" [Lf "v1", Lf "v0"] 
     -- predicate var
     newVar (Lf "predV") boolTy
     runGenV "declareVar" "decPredV" [Lf "predV"]
     genFunV "appPred0" predf (Lf "v0") v0 (Lf "predV")
     genFunV "appPred1" predf (Lf "v1") v0 (Lf "predV")
     genFunV "appPred2" predf (Lf "v2") v0 (Lf "predV")
     -- get env vars (appart from outVar and streamVar) from v0
     -- and pass along/make public here (e.g. vecmapType)
       -- get node to import env from
     inEnv <- (do
         publicEnvs <- gets genObjMembers ; 
         return $ (lookupNode ("loop template: can't find env for input node " ++ (show v0)) (fst $ treeLabel v0) publicEnvs) `DM.difference` varsToExclude)
     mapM (\(vid, val) -> setVal out vid val) $ DM.toList inEnv
     --runGenV "declareVar" 
     -- create output var if doesn't already exist
     --     decName  publicName localName type
     --ifnVar "decOut" outVarName (Lf "") t3
     -- when gen is called, generate assignment
     setFun out "gen" nt (\_ -> do
       output "main" $
         "// begin <tem>\n"++
         --"<decPredV>\n<appPred0>\n<decBuffs>\n<decOut>\nif (<predV>) {\n<appNext0>\n} else {\n<copyBuff2>\n}\n"++
         "<decPredV><appPred0>\n"++
         "<decBuffs>\n<decOut>\n"++ 
         "if (<predV>) {\n"++
         "  <appNext0>\n"++
         "  <appPred1>\n"++
         "  while (<predV>) {\n"++
         "    <appNext1>\n"++
         "    <appPred2>\n"++
         "    if (!<predV>) {\n"++
         "      <copyBuff>\n"++
         "      break;\n"++
         "    }\n"++
         "    <appNext2>\n"++
         "    <appPred1>\n"++
         "  }\n"++
         "}\n"++
         "// end <tem>\n"
       return ())
t01 t n = terr' t n

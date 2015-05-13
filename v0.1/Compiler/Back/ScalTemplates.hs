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
module Compiler.Back.ScalTemplates where

import Compiler.Back.Graph
import Compiler.Back.GenDecls
import Compiler.Back.Gen
import Compiler.Back.Templates

import Control.Monad.State.Strict (get)
import Control.Monad.Catch
import Data.List (intercalate)

-- scalar function templates

scalTemplates :: (Monad m, MonadCatch m) => [(Id, Template m)]
scalTemplates = 
  (map (\(n,op) -> (n, unTem op)) unOps) ++
  (map (\(n,op) -> (n, binTem op)) binOps) ++ 
  [("print", t0)]

unOps :: [(String, String)]
unOps = [
  ("not", "!<av>"),

  ("intToFloat", "(double)<av>"),
  ("floatToInt", "(int)<av>"),

  ("negi", "-<av>"),
  ("maxiv", "std::numeric_limits<int>::max()"),
  ("miniv", "std::numeric_limits<int>::min()"),

  ("negf", "-<av>"),
  ("randf", "(double)rand() / RAND_MAX"),
  ("sqrt", "sqrt(<av>)"),
  ("maxfv", "std::numeric_limits<double>::max()"),
  ("minfv", "std::numeric_limits<double>::min()")
  ]

-- |unary scalar operation template
unTem :: (Monad m, MonadCatch m) => String -> Template m
unTem unOp  
   (t1 :-> t3)
   (LFun _ a   c) = do
     -- get input vars
     if t1 /= nullTy
     then getVar (Lf "av") a outVarName
     else return ()
     -- create output var if doesn't already exist
     --     decName  publicName localName type
     ifnVar "decOut" outVarName (Lf "cv") t3
     -- when gen is called, generate assignment
     setFun c "gen" Nothing (\_ -> do
       outputDecl c "<decOut>"
       output "main" $ "<cv> = " ++ unOp ++ ";\n"
       return ())
unTem _ t n = terr' t n

binOps :: [(String, String)]
binOps = [
  ("eq", "(<av>) == (<bv>)"), -- polymorphic eq
  ("lt", "(<av>) < (<bv>)"), -- polymorphic less than
  ("max", "((<av> < <bv>) ? <bv> : <av>)"), -- polymorphic max and min
  ("min", "((<av> < <bv>) ? <av> : <bv>)"),

  ("addi", "<av> + <bv>"), 
  ("subi", "<av> - <bv>"), 
  ("muli", "<av> * <bv>"), 
  ("divi", "<av> / <bv>"), 
  ("modi", "<av> % <bv>"), 
  ("mini", "min(<av>, <bv>)"),
  ("maxi", "max(<av>, <bv>)"),
  ("powi", "ipow(<av>, <bv>)"),
  ("shri", "<av> >> <bv>"),
  ("shli", "<av> << <bv>"),

  ("eqi", "<av> == <bv>"),
  ("gti", "<av> > <bv>"),
  ("gtei", "<av> >= <bv>"),
  ("lti", "<av> < <bv>"),
  ("ltei", "<av> <= <bv>"),

  ("addf", "<av> + <bv>"), 
  ("subf", "<av> - <bv>"), 
  ("mulf", "<av> * <bv>"), 
  ("divf", "<av> / <bv>"), 
  ("minf", "min(<av>, <bv>)"),
  ("maxf", "max(<av>, <bv>)"),
  ("powf", "pow(<av>, <bv>)"),

  ("eqf", "<av> == <bv>"),
  ("gtf", "<av> > <bv>"),
  ("gtef", "<av> >= <bv>"),
  ("ltf", "<av> < <bv>"),
  ("ltef", "<av> <= <bv>"),

  ("and", "<av> && <bv>"),
  ("or", "<av> || <bv>"),

  ("mandel", "mandelbrot_xy(<av>, <bv>)")

  ]

-- |binary scalar operation template
binTem :: (Monad m, MonadCatch m) => String -> Template m
binTem binOp  
   (Tup [t1, t2] :->  t3)
   nodes@(LFun _ (LTup _ [a, b])        c)
   | t1 == t2 = do
     tn <- getTemplateName
     --if (fst $ treeLabel b) == 3439 --tn == "divf" || tn == "mulf"
     --then do
     --  st <- get
     --  error $ "NODE 3439:\n" ++ (intercalate "\n\n" $ map show $ genGraphs st) -- error $ tn ++ " template:\n" ++ (show nodes) 
     --else return () --getVar (Lf "bv") b outVarName
     -- get input vars
     getVar (Lf "av") a outVarName
     getVar (Lf "bv") b outVarName
     -- create output var if doesn't already exist
     --     decName  publicName localName type
     ifnVar "decOut" outVarName (Lf "cv") t3
     -- when gen is called, generate assignment
     setFun c "gen" Nothing (\_ -> do
       outputDecl c "<decOut>"
       output "main" $ "<cv> = " ++ binOp ++ ";\n"
       return ())
binTem _ t n = terr' t n

-- |print template
t0 :: (Monad m, MonadCatch m) => Template m
t0 (t1 :-> t3)
   (LFun _ a   c) = do
     -- get input vars
     getVar (Lf "av") a outVarName
     -- pack it in a struct
     newStructVar (Lf "as") t1
     runGenV "declareVar" "decAs" [Lf "as"] 
     runGenV "assignVar" "packAs" [Lf "as", Lf "av"] 
     -- when gen is called, generate assignment
     setFun c "gen" Nothing (\_ -> do
       output "main" $ "if (thisRank == rootRank) { <decAs>\n<packAs>\nprintVal(<as>);\nprintVal(\"\\n\"); }\n"
       return ())
t0 t n = terr' t n



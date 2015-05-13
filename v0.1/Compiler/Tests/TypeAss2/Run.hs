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

import Compiler.Front.Common
import Compiler.Front.Indices (IdxMonad)
import Compiler.Front.Front
import Compiler.Front.ExprTree hiding (Var)
import Compiler.Front.SrcLexer
import Compiler.Front.SrcParser

import Compiler.Types2.Types
import Compiler.Types2.TermLanguage 
import Compiler.Types2.TypeAssignment
import Compiler.Types2.DepTypeAssignment (assignDepTypes2, solveDepConstrs2, solveDepConstrs3)
import Compiler.Types2.EmbeddedFunctions 

import Data.List (isSuffixOf)
import System.Directory
import Control.Monad.State.Strict (lift)
import qualified Data.IntMap as IM

-- |namedTy takes a string and list of child types
-- |and returns the type term for it.
namedTy :: String -> [TyTerm] -> TyTerm
namedTy n l = Term (Tok (Ty n)) l

tup :: [TyTerm] -> TyTerm
tup l = Term TupTok l

nameTy n = namedTy n []

passFuns = [
    (nameTy "FFst" :=: namedTy "FSeq" [nameTy "FId", nameTy "FFst"]),
    (nameTy "FSnd" :=: namedTy "FSeq" [nameTy "FSnd", nameTy "FId"]),
    (nameTy "FLft" :=: namedTy "FDup" [namedTy "FSeq" [nameTy "FFst", nameTy "FFst"], namedTy "FSeq" [nameTy "FFst", nameTy "FSnd"]]),
    (nameTy "FRht" :=: namedTy "FDup" [namedTy "FSeq" [nameTy "FSnd", nameTy "FFst"], namedTy "FSeq" [nameTy "FSnd", nameTy "FSnd"]]),
    --(namedTy "FSeq" [nameTy "FFst", Var 1] :=: namedTy "FFun" [Var 2, namedTy "FApp" [Var 3, namedTy "FApp" [nameTy "FFst", Var 2]]])
    (namedTy "FSeq" [Var 4, nameTy "FFst"] :=: namedTy "FSeq" [nameTy "FFst", Var 5]),
    (namedTy "FBoth" [nameTy "FFst", nameTy "FSnd"] :=: nameTy "FFst"),
    (namedTy "FBoth" [nameTy "FFst", nameTy "FSnd"] :=: nameTy "FSnd"),
    (namedTy "FBoth" [nameTy "FFst", nameTy "FSnd"] :=: namedTy "FBoth" [nameTy "FLft", nameTy "FSnd"]),
    (nameTy "FFst" :=: namedTy "GFst" [nameTy "FLft"]),
    (namedTy "GSnd" [nameTy "FRht"] :=: nameTy "FSnd"),
    (nameTy "FSnd" :=: namedTy "GFst" [nameTy "FRht"]),
    (namedTy "GSnd" [nameTy "FLft"] :=: nameTy "FFst"),
    (namedTy "GFst" [Var 6] :=: nameTy "FFst"),
    (Var 6 :=: nameTy "FLft"),
    (namedTy "GRem" [nameTy "FFst"] :=: nameTy "FSnd"),
    (namedTy "GRem" [nameTy "FSnd"] :=: nameTy "FFst"),
    (namedTy "GRem" [nameTy "FLft"] :=: nameTy "FRht"), -- does not have to pass by def of GRem
    (namedTy "GRem" [nameTy "FRht"] :=: nameTy "FLft"),  -- ditto
    (namedTy "GFst" [namedTy "GFst" [nameTy "FLft"]] :=: nameTy "FId"),
    (namedTy "FSeq" [nameTy "FLft", nameTy "FFst"] :=: namedTy "FFun" [tup [tup [tup [Var 9, Var 10], tup [Var 11, Var 12]], Var 8], tup [Var 9, Var 11]]),
    (namedTy "GFst" [namedTy "FSeq" [nameTy "FLft", nameTy "FFst"]] :=: nameTy "FLft"),
    (namedTy "GFst" [namedTy "FSeq" [nameTy "FRht", nameTy "FFst"]] :=: nameTy "FRht"),
    (namedTy "GSnd" [namedTy "FSeq" [nameTy "FLft", nameTy "FFst"]] :=: nameTy "FNull"),
    (namedTy "GSnd" [namedTy "FSeq" [nameTy "FRht", nameTy "FFst"]] :=: nameTy "FNull"),
    (namedTy "GFst" [namedTy "FSeq" [nameTy "FLft", nameTy "FSnd"]] :=: nameTy "FNull"),
    (namedTy "GFst" [namedTy "FSeq" [nameTy "FRht", nameTy "FSnd"]] :=: nameTy "FNull"),
    (namedTy "GSnd" [namedTy "FSeq" [nameTy "FLft", nameTy "FSnd"]] :=: nameTy "FLft"),
    (namedTy "GSnd" [namedTy "FSeq" [nameTy "FRht", nameTy "FSnd"]] :=: nameTy "FRht"),
    -- (namedTy "GFst" [namedTy "FSeq" [Var 13, nameTy "FFst"]] :=: Var 13) -- circular constraint
    (namedTy "GFst" [Var 7] :=: nameTy "FFst"),
    (Var 7 :=: namedTy "GFst" [namedTy "FSeq" [Var 6, Var 6]])
  ]

failFuns = [
    (nameTy "FFst" :=: namedTy "FSeq" [nameTy "FFst", nameTy "FFst"])
  ]

main2 :: IdxMonad IO ()
main2 = do
  lift $ putStr "Type assignment 2:\n"  

  -- load types
  curDir <- lift $ getCurrentDirectory
  let typesPath = curDir ++ "/Compiler/Tests/TypeAss2/types.txt"
  lift $ putStr $ "Load type defs from: " ++ typesPath ++ "\n"
  (varIds, typeDefs) <- loadDepTypes typesPath -- varIds maps var names to idxs, typeDefs maps var ids to type schemes

  -- load source file
  {-let testFile = curDir ++ "/Compiler/Tests/TypeAss2/program.flocc"
  ast <- parseSrcFile varIds testFile

  -- perform type assignment
  res <- assignDepTypes2 (IM.fromList typeDefs) ast
  case res of
    Left astTypes -> do
      lift $ putStr "Success:\n"
      lift $ putStr $ showExprWithTypes astTypes ast
    Right (con, astTypes) -> do
      error $ "Type assignment failed on constraint:\n" ++ (show $ fmap showEmbeddedFuns $ fmap stripTermLabelsRec con) ++ "\n" ++ (showP astTypes) -}

  -- solve constrs
  res <- solveDepConstrs3 IM.empty (IM.fromList typeDefs) [] passFuns
  case res of
    Left astTypes -> do
      lift $ putStr "Success:\n"
      --lift $ putStr $ showExprWithTypes astTypes ast
    Right (con, astTypes) -> do
      error $ "Type assignment failed on constraint:\n" ++ (show $ fmap showEmbeddedFuns $ fmap stripTermLabelsRec con) ++ "\n" ++ (showP astTypes)

  lift $ putStr "\n\n"
  return ()

main :: IO ()
main = do
  evalIdxStateT 0 main2
  return ()

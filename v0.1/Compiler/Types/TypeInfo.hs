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
module Compiler.Types.TypeInfo where

import Data.List (nub)
import Data.Maybe (fromMaybe)

import Compiler.Types.TermLanguage (Term(..), FunctionToken(Tok), Scheme(..))
import Compiler.Types.TypeAssignment (TyToken(Ty), TyTerm)

namedTy :: String -> [TyTerm] -> TyTerm
namedTy name l = (Term (Tok (Ty name)) l)

-- Meta-information about front-end types.

-- Remember to add distCol to FromFront2:translateTypes

typeNames = distColTypeNames

distColTypeNames = ["DArr", "DMap", "DList"]

typesContainingFuns = nub $ map fst funLocations

type TyLocs = [(String, Int)]

numTypeParams = [
  ("Map", 2), ("List", 1), ("Arr", 2),
  ("DMap", 7), ("DArr", 7), ("DList", 5), -- dist collections
  ("Null", 0), ("Int", 0), ("Float", 0), ("Bool", 0), -- scalars
  ("Stm", 0), ("Vec", 0), ("Arr", 0),  -- modes
  ("VNull", 0), ("VTrue", 0), ("VFalse", 0), ("VInt", 1), -- function values
  ("FFun", 2), ("FFst", 0), ("FSnd", 0), ("FId", 0), -- functions
  ("FApp", 2), ("FDup", 2), ("FSeq", 2), ("FPair", 2), ("FBoth", -1), ("FNull", 0),
  ("FSwap", 0), ("FLft", 0), ("FRht", 0),
  ("Cyc", 0), ("Blk", 0), -- partition modes
  ("Intersect", 2) -- intersection of two dim identifiers
  ] :: TyLocs

funLocations = partFunLocations ++ layoutFunLocations

partFunLocations = [("DMap", 4), ("DArr", 4)] :: TyLocs

layoutFunLocations = [("DMap", 3), ("DArr", 3)] :: TyLocs

typesContainingDims = nub $ map fst dimLocations

dimLocations = partDimLocations ++ mirrDimLocations

partDimLocations = [("DMap", 5), ("DArr", 5), ("DList", 3)] :: TyLocs

mirrDimLocations = [("DMap", 6), ("DArr", 6), ("DList", 4)] :: TyLocs

type TyModes = [((String, Int),[String])]  

typesContainingModes = nub $ map (fst . fst) typeModeInfo

typeModeInfo = [
    (("DMap", 0), ["Vec", "Stm", "Tree", "Hash"]),
    (("DArr", 0), ["Arr", "Stm"]),
    (("DList", 0), ["Stm", "Vec", "List", "Arr"])
  ] :: TyModes

typeDefaults = [
  (("DList", 2), namedTy "blk" [])
  ]

-- Helper functions

numParams :: String -> Int
numParams name = fromMaybe (error $ "Types/TypeInfo/Please add num type params for " ++ name) $ lookup name numTypeParams

funs :: String -> [Int]
funs name = map snd $ filter (\(n,_) -> n == name) funLocations

partFuns :: String -> [Int]
partFuns name = map snd $ filter (\(n,_) -> n == name) partFunLocations

layFuns :: String -> [Int]
layFuns name = map snd $ filter (\(n,_) -> n == name) layoutFunLocations

typeModes :: String -> [(Int, [String])]
typeModes name = map (\((n,i),l) -> (i,l)) $ filter (\((n,i),l) -> n == name) typeModeInfo

dimLocs :: String -> [Int]
dimLocs name = map snd $ filter (\(n,i) -> n == name) dimLocations

typeDefault :: String -> Int -> Maybe TyTerm
typeDefault name idx = lookup (name, idx) typeDefaults

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
{-# OPTIONS_GHC -w #-}
module Compiler.Types2.TypeParser ( parseTypes, TypeDec, typeDecToScheme,
  numberTypes, typeNameMap, typeEnv, typeDecsToSchemeExEnv,
  generateNamedSchemeEnv, generateNamedSchemeExEnv ) where

import Compiler.Types2.TypeLexer
import Compiler.Types2.TermLanguage 
import Compiler.Types2.TermBuilder
import Compiler.Types2.TypeAssignment

import Compiler.Front.Common (dtvids, runIdxStateT)
import Compiler.Front.Indices ( Idx, IdxSet, newid'' )
import Compiler.Front.ExprTree ( IdxTree(..), newExprVarId )

import Data.Functor.Identity ( Identity, runIdentity )
import Control.Monad.State.Strict ( StateT, lift, evalStateT, get, modify )
import qualified Data.Map.Strict as Data.Map

-- parser produced by Happy Version 1.18.8

data HappyAbsSyn t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19
	= HappyTerminal (PosnToken)
	| HappyErrorToken Int
	| HappyAbsSyn4 t4
	| HappyAbsSyn5 t5
	| HappyAbsSyn6 t6
	| HappyAbsSyn7 t7
	| HappyAbsSyn8 t8
	| HappyAbsSyn9 t9
	| HappyAbsSyn10 t10
	| HappyAbsSyn11 t11
	| HappyAbsSyn12 t12
	| HappyAbsSyn13 t13
	| HappyAbsSyn14 t14
	| HappyAbsSyn15 t15
	| HappyAbsSyn16 t16
	| HappyAbsSyn17 t17
	| HappyAbsSyn18 t18
	| HappyAbsSyn19 t19

action_0 (20) = happyShift action_4
action_0 (4) = happyGoto action_5
action_0 (6) = happyGoto action_2
action_0 (7) = happyGoto action_3
action_0 _ = happyReduce_5

action_1 (20) = happyShift action_4
action_1 (6) = happyGoto action_2
action_1 (7) = happyGoto action_3
action_1 _ = happyFail

action_2 (27) = happyShift action_10
action_2 (5) = happyGoto action_7
action_2 (8) = happyGoto action_8
action_2 (9) = happyGoto action_9
action_2 _ = happyReduce_2

action_3 (20) = happyShift action_6
action_3 _ = happyReduce_6

action_4 _ = happyReduce_7

action_5 (31) = happyAccept
action_5 _ = happyFail

action_6 _ = happyReduce_8

action_7 (20) = happyShift action_4
action_7 (6) = happyGoto action_17
action_7 (7) = happyGoto action_18
action_7 _ = happyReduce_5

action_8 _ = happyReduce_3

action_9 (23) = happyShift action_14
action_9 (24) = happyShift action_15
action_9 (27) = happyShift action_16
action_9 (10) = happyGoto action_11
action_9 (17) = happyGoto action_12
action_9 (19) = happyGoto action_13
action_9 _ = happyReduce_11

action_10 _ = happyReduce_10

action_11 (28) = happyShift action_22
action_11 _ = happyFail

action_12 _ = happyReduce_12

action_13 _ = happyReduce_30

action_14 _ = happyReduce_29

action_15 (23) = happyShift action_14
action_15 (24) = happyShift action_15
action_15 (27) = happyShift action_16
action_15 (17) = happyGoto action_20
action_15 (18) = happyGoto action_21
action_15 (19) = happyGoto action_13
action_15 _ = happyFail

action_16 _ = happyReduce_34

action_17 _ = happyReduce_1

action_18 (20) = happyShift action_6
action_18 (27) = happyShift action_10
action_18 (8) = happyGoto action_19
action_18 (9) = happyGoto action_9
action_18 _ = happyReduce_6

action_19 _ = happyReduce_4

action_20 _ = happyReduce_32

action_21 (22) = happyShift action_25
action_21 (25) = happyShift action_26
action_21 _ = happyFail

action_22 (29) = happyShift action_24
action_22 (11) = happyGoto action_23
action_22 _ = happyReduce_13

action_23 (24) = happyShift action_32
action_23 (26) = happyShift action_33
action_23 (27) = happyShift action_16
action_23 (12) = happyGoto action_30
action_23 (19) = happyGoto action_31
action_23 _ = happyFail

action_24 (27) = happyShift action_16
action_24 (16) = happyGoto action_28
action_24 (19) = happyGoto action_29
action_24 _ = happyFail

action_25 (23) = happyShift action_14
action_25 (24) = happyShift action_15
action_25 (27) = happyShift action_16
action_25 (17) = happyGoto action_27
action_25 (19) = happyGoto action_13
action_25 _ = happyFail

action_26 _ = happyReduce_31

action_27 _ = happyReduce_33

action_28 (22) = happyShift action_38
action_28 (30) = happyShift action_39
action_28 _ = happyFail

action_29 _ = happyReduce_27

action_30 (21) = happyShift action_37
action_30 _ = happyReduce_9

action_31 _ = happyReduce_15

action_32 (24) = happyShift action_32
action_32 (26) = happyShift action_33
action_32 (27) = happyShift action_16
action_32 (12) = happyGoto action_35
action_32 (15) = happyGoto action_36
action_32 (19) = happyGoto action_31
action_32 _ = happyReduce_24

action_33 (13) = happyGoto action_34
action_33 _ = happyReduce_19

action_34 (24) = happyShift action_46
action_34 (26) = happyShift action_47
action_34 (27) = happyShift action_16
action_34 (14) = happyGoto action_44
action_34 (19) = happyGoto action_45
action_34 _ = happyReduce_16

action_35 (21) = happyShift action_37
action_35 _ = happyReduce_26

action_36 (22) = happyShift action_42
action_36 (25) = happyShift action_43
action_36 _ = happyFail

action_37 (24) = happyShift action_32
action_37 (26) = happyShift action_33
action_37 (27) = happyShift action_16
action_37 (12) = happyGoto action_41
action_37 (19) = happyGoto action_31
action_37 _ = happyFail

action_38 (27) = happyShift action_16
action_38 (19) = happyGoto action_40
action_38 _ = happyFail

action_39 _ = happyReduce_14

action_40 _ = happyReduce_28

action_41 (21) = happyShift action_37
action_41 _ = happyReduce_17

action_42 (24) = happyShift action_32
action_42 (26) = happyShift action_33
action_42 (27) = happyShift action_16
action_42 (12) = happyGoto action_49
action_42 (19) = happyGoto action_31
action_42 _ = happyFail

action_43 _ = happyReduce_18

action_44 _ = happyReduce_20

action_45 _ = happyReduce_22

action_46 (24) = happyShift action_32
action_46 (26) = happyShift action_33
action_46 (27) = happyShift action_16
action_46 (12) = happyGoto action_35
action_46 (15) = happyGoto action_48
action_46 (19) = happyGoto action_31
action_46 _ = happyReduce_24

action_47 _ = happyReduce_21

action_48 (22) = happyShift action_42
action_48 (25) = happyShift action_50
action_48 _ = happyFail

action_49 (21) = happyShift action_37
action_49 _ = happyReduce_25

action_50 _ = happyReduce_23

happyReduce_1 = happySpecReduce_3  4 happyReduction_1
happyReduction_1 _
	(HappyAbsSyn5  happy_var_2)
	_
	 =  HappyAbsSyn4
		 (reverse happy_var_2
	)
happyReduction_1 _ _ _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_0  5 happyReduction_2
happyReduction_2  =  HappyAbsSyn5
		 ([]
	)

happyReduce_3 = happySpecReduce_1  5 happyReduction_3
happyReduction_3 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn5
		 ([happy_var_1]
	)
happyReduction_3 _  = notHappyAtAll 

happyReduce_4 = happySpecReduce_3  5 happyReduction_4
happyReduction_4 (HappyAbsSyn8  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn5
		 (happy_var_3 : happy_var_1
	)
happyReduction_4 _ _ _  = notHappyAtAll 

happyReduce_5 = happySpecReduce_0  6 happyReduction_5
happyReduction_5  =  HappyAbsSyn6
		 ([]
	)

happyReduce_6 = happySpecReduce_1  6 happyReduction_6
happyReduction_6 _
	 =  HappyAbsSyn6
		 ([]
	)

happyReduce_7 = happySpecReduce_1  7 happyReduction_7
happyReduction_7 _
	 =  HappyAbsSyn7
		 ([]
	)

happyReduce_8 = happySpecReduce_2  7 happyReduction_8
happyReduction_8 _
	_
	 =  HappyAbsSyn7
		 ([]
	)

happyReduce_9 = happyMonadReduce 5 8 happyReduction_9
happyReduction_9 ((HappyAbsSyn12  happy_var_5) `HappyStk`
	(HappyAbsSyn11  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn10  happy_var_2) `HappyStk`
	(HappyAbsSyn9  happy_var_1) `HappyStk`
	happyRest) tk
	 = happyThen ((
          do ret <- get 
             let ret' = varEnvDiff ret (getIdxPatVarEnv happy_var_2)
             case (happy_var_4, ret') of
             -- if there is no forall but there are vars referenced
             -- that are not in the idx pattern, return all those 
               ([], a:b) -> return (happy_var_1,happy_var_2,ret',happy_var_5)
             -- else return the forall
               _         -> return (happy_var_1,happy_var_2,happy_var_4,happy_var_5))
	) (\r -> happyReturn (HappyAbsSyn8 r))

happyReduce_10 = happyMonadReduce 1 9 happyReduction_10
happyReduction_10 ((HappyTerminal (PosnTok _ _ _ (TokVar happy_var_1))) `HappyStk`
	happyRest) tk
	 = happyThen (( do resetVarEnv ; return happy_var_1)
	) (\r -> happyReturn (HappyAbsSyn9 r))

happyReduce_11 = happySpecReduce_0  10 happyReduction_11
happyReduction_11  =  HappyAbsSyn10
		 (IdxNub defId
	)

happyReduce_12 = happySpecReduce_1  10 happyReduction_12
happyReduction_12 (HappyAbsSyn17  happy_var_1)
	 =  HappyAbsSyn10
		 (happy_var_1
	)
happyReduction_12 _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_0  11 happyReduction_13
happyReduction_13  =  HappyAbsSyn11
		 ([]
	)

happyReduce_14 = happySpecReduce_3  11 happyReduction_14
happyReduction_14 _
	(HappyAbsSyn16  happy_var_2)
	_
	 =  HappyAbsSyn11
		 (reverse happy_var_2
	)
happyReduction_14 _ _ _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_1  12 happyReduction_15
happyReduction_15 (HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn12
		 (Var (snd happy_var_1)
	)
happyReduction_15 _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_2  12 happyReduction_16
happyReduction_16 (HappyAbsSyn13  happy_var_2)
	(HappyTerminal (PosnTok _ _ _ (TokName happy_var_1)))
	 =  HappyAbsSyn12
		 (ty happy_var_1 (reverse happy_var_2)
	)
happyReduction_16 _ _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_3  12 happyReduction_17
happyReduction_17 (HappyAbsSyn12  happy_var_3)
	_
	(HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn12
		 (fun happy_var_1 happy_var_3
	)
happyReduction_17 _ _ _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_3  12 happyReduction_18
happyReduction_18 _
	(HappyAbsSyn15  happy_var_2)
	_
	 =  HappyAbsSyn12
		 (if length happy_var_2 == 1 then head happy_var_2 else (if length happy_var_2 == 0 then nullTy else tup $ reverse happy_var_2)
	)
happyReduction_18 _ _ _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_0  13 happyReduction_19
happyReduction_19  =  HappyAbsSyn13
		 ([]
	)

happyReduce_20 = happySpecReduce_2  13 happyReduction_20
happyReduction_20 (HappyAbsSyn14  happy_var_2)
	(HappyAbsSyn13  happy_var_1)
	 =  HappyAbsSyn13
		 (happy_var_2 : happy_var_1
	)
happyReduction_20 _ _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_1  14 happyReduction_21
happyReduction_21 (HappyTerminal (PosnTok _ _ _ (TokName happy_var_1)))
	 =  HappyAbsSyn14
		 (if happy_var_1 == "UniVar" then (UniVar 0) else ty happy_var_1 []
	)
happyReduction_21 _  = notHappyAtAll 

happyReduce_22 = happySpecReduce_1  14 happyReduction_22
happyReduction_22 (HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn14
		 (Var (snd happy_var_1)
	)
happyReduction_22 _  = notHappyAtAll 

happyReduce_23 = happySpecReduce_3  14 happyReduction_23
happyReduction_23 _
	(HappyAbsSyn15  happy_var_2)
	_
	 =  HappyAbsSyn14
		 (if length happy_var_2 == 1 then head happy_var_2 else (if length happy_var_2 == 0 then nullTy else tup $ reverse happy_var_2)
	)
happyReduction_23 _ _ _  = notHappyAtAll 

happyReduce_24 = happySpecReduce_0  15 happyReduction_24
happyReduction_24  =  HappyAbsSyn15
		 ([]
	)

happyReduce_25 = happySpecReduce_3  15 happyReduction_25
happyReduction_25 (HappyAbsSyn12  happy_var_3)
	_
	(HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn15
		 (happy_var_3 : happy_var_1
	)
happyReduction_25 _ _ _  = notHappyAtAll 

happyReduce_26 = happySpecReduce_1  15 happyReduction_26
happyReduction_26 (HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn15
		 ([happy_var_1]
	)
happyReduction_26 _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_1  16 happyReduction_27
happyReduction_27 (HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn16
		 ([(fst happy_var_1, snd happy_var_1)]
	)
happyReduction_27 _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_3  16 happyReduction_28
happyReduction_28 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn16  happy_var_1)
	 =  HappyAbsSyn16
		 ((fst happy_var_3, snd happy_var_3) : happy_var_1
	)
happyReduction_28 _ _ _  = notHappyAtAll 

happyReduce_29 = happySpecReduce_1  17 happyReduction_29
happyReduction_29 _
	 =  HappyAbsSyn17
		 (IdxNub defId
	)

happyReduce_30 = happySpecReduce_1  17 happyReduction_30
happyReduction_30 (HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn17
		 (IdxLeaf defId (snd happy_var_1) (fst happy_var_1)
	)
happyReduction_30 _  = notHappyAtAll 

happyReduce_31 = happySpecReduce_3  17 happyReduction_31
happyReduction_31 _
	(HappyAbsSyn18  happy_var_2)
	_
	 =  HappyAbsSyn17
		 (IdxTup defId $ reverse happy_var_2
	)
happyReduction_31 _ _ _  = notHappyAtAll 

happyReduce_32 = happySpecReduce_1  18 happyReduction_32
happyReduction_32 (HappyAbsSyn17  happy_var_1)
	 =  HappyAbsSyn18
		 ([happy_var_1]
	)
happyReduction_32 _  = notHappyAtAll 

happyReduce_33 = happySpecReduce_3  18 happyReduction_33
happyReduction_33 (HappyAbsSyn17  happy_var_3)
	_
	(HappyAbsSyn18  happy_var_1)
	 =  HappyAbsSyn18
		 (happy_var_3 : happy_var_1
	)
happyReduction_33 _ _ _  = notHappyAtAll 

happyReduce_34 = happyMonadReduce 1 19 happyReduction_34
happyReduction_34 ((HappyTerminal (PosnTok _ _ _ (TokVar happy_var_1))) `HappyStk`
	happyRest) tk
	 = happyThen (( do id <- getVarId happy_var_1; 
                                         return (happy_var_1, id))
	) (\r -> happyReturn (HappyAbsSyn19 r))

happyNewToken action sts stk [] =
	action 31 31 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	PosnTok _ _ _ TokEOL -> cont 20;
	PosnTok _ _ _ TokArrow -> cont 21;
	PosnTok _ _ _ TokComma -> cont 22;
	PosnTok _ _ _ TokUnderscore -> cont 23;
	PosnTok _ _ _ TokLParen -> cont 24;
	PosnTok _ _ _ TokRParen -> cont 25;
	PosnTok _ _ _ (TokName happy_dollar_dollar) -> cont 26;
	PosnTok _ _ _ (TokVar happy_dollar_dollar) -> cont 27;
	PosnTok _ _ _ TokColon -> cont 28;
	PosnTok _ _ _ TokForall -> cont 29;
	PosnTok _ _ _ TokImplies -> cont 30;
	_ -> happyError' (tk:tks)
	}

happyError_ 31 tk tks = happyError' tks
happyError_ _ tk tks = happyError' (tk:tks)

happyThen :: () => MonadType a -> (a -> MonadType b) -> MonadType b
happyThen = (>>=)
happyReturn :: () => a -> MonadType a
happyReturn = (return)
happyThen1 m k tks = (>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> MonadType a
happyReturn1 = \a tks -> (return) a
happyError' :: () => [(PosnToken)] -> MonadType a
happyError' = parseError

parseInternal tks = happySomeParser where
  happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


defId :: Idx
defId = -1

-- |Shorthand to create new type terms
ty :: String -> [TyTerm] -> TyTerm
ty s l = Term (Tok (Ty s)) l

-- |Parse error function
parseError :: [PosnToken] -> a
parseError ((PosnTok _ lineNum colNum _):tl) = error $ "Type file parse error on line " ++ (show lineNum)
  ++ ":" ++ (show colNum) ++ " near '"++ (concat $ map show $ take 10 $ takeWhile (\(PosnTok _ _ _ t) -> t /= TokEOL) tl) ++ "'"

-- |idxTreeToIdTree takes an IdxTree and returns an IdTree 
-- | of all it's var ids.
idxTreeToIdTree :: IdxTree -> IdTree
idxTreeToIdTree it = case it of
  (IdxTup _ l)      -> IdTup $ map idxTreeToIdTree l
  (IdxLeaf _ vid _) -> IdLeaf vid
  (IdxNub _)        -> IdBlank

-- |Monad type of parser
type MonadType = StateT [(String, Idx)] (StateT IdxSet Identity)

-- |The return type of the parse
type TypeDec = (String, IdxTree, [(String, Idx)], TyTerm)

-- |Returns the type scheme of a type declaration
typeDecToScheme :: TypeDec -> TyScheme
typeDecToScheme (_,_,boundVars,ty) = 
  scm (map (\i -> Var i) $ snd $ unzip boundVars) ty

-- |typeDecToSchemeEx takes a type declaration and returns an 
-- |Scheme extended to include an IdTree of qualified variables.
typeDecToSchemeEx :: TypeDec -> TySchemeEx
typeDecToSchemeEx dec = SchemeEx (idxTreeToIdTree idxTree) scheme
  where (_,idxTree,_,_) = dec
        scheme = typeDecToScheme dec

-- |If the string exists in the state, then returns current binding or otherwise
-- |creates a new binding.
getVarId :: String -> MonadType Idx
getVarId s = do
  env <- get
  case lookup s env of
    Just idx -> return idx
    Nothing  -> do
      idx <- lift $ newid'' dtvids --vids --dtids
      modify (\env -> (s,idx):env)
      return idx

-- |Wipes all current bindings ready for the next type declaration
resetVarEnv :: MonadType ()
resetVarEnv = do
  modify (\env -> [])
  return ()

-- |Gets the var env defined by an idx pattern
getIdxPatVarEnv :: IdxTree -> [(String,Idx)]
getIdxPatVarEnv ip = case ip of
  IdxNub _ -> []
  IdxLeaf _ vid name -> [(name, vid)]
  IdxTup _ l -> concat $ map getIdxPatVarEnv l

-- |Performs set difference on var environments
varEnvDiff :: [(String, Idx)] -> [(String, Idx)] -> [(String,Idx)]
varEnvDiff a b = Data.Map.toList $ 
  (Data.Map.fromList a) Data.Map.\\ (Data.Map.fromList b)

-- |Parse method to export as does some basic post processing
-- |using cleanUpTuples
--parseTypes :: [PosnToken] -> StateT IdxSet Identity [TypeDec]
--parseTypes tl = evalStateT (parseInternal tl) []
parseTypes' :: String -> StateT IdxSet Identity [TypeDec]
parseTypes' s = evalStateT (parseInternal $ scanTypes s) []
--runIdentity $ evalIdxStateT 

parseTypes :: Monad m => String -> StateT IdxSet m [TypeDec]
parseTypes s = do
  let (types, idxset) = runIdentity $ runIdxStateT 0 (parseTypes' s)
  --error $ show idxset
  modify (\_ -> idxset)
  return types

-- |Number all types in a type dec list
numberTypes :: Monad m => [TypeDec] -> StateT IdxSet m [(Idx, TypeDec)]
numberTypes tl = do
  tl' <- mapM (\t -> do vid <- newExprVarId; return (vid,t)) tl
  return tl'

-- |Return a map of names to type env indices
typeNameMap :: [(Idx, TypeDec)] -> [(String, Idx)]
typeNameMap tl = map (\(i,(n,_,_,_)) -> (n,i)) tl

-- |Return a map of type indices to type schemes
typeEnv :: [(Idx, TypeDec)] -> [(Idx, TyScheme)]
typeEnv tl = map (\(i,tydec) -> (i, typeDecToScheme tydec)) tl

-- |Returns a named list of type schemes.
generateNamedSchemeEnv :: [TypeDec] -> [(String, TyScheme)]
generateNamedSchemeEnv tl = map (\tyDec@(name,_,_,_) -> (name, typeDecToScheme tyDec)) tl

-- |typeDecsToSchemeEnv takes an associative list of type declarations
-- |and returns an associative lift of SchemeEx values.
typeDecsToSchemeExEnv :: [(Idx, TypeDec)] -> [(Idx, TySchemeEx)]
typeDecsToSchemeExEnv tl = map (\(i,tydec) -> (i, typeDecToSchemeEx tydec)) tl

-- |Returns a named list of type scheme ex's.
generateNamedSchemeExEnv :: [TypeDec] -> [(String, TySchemeEx)]
generateNamedSchemeExEnv tl = map (\tyDec@(name,_,_,_) -> (name, typeDecToSchemeEx tyDec)) tl
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 30 "templates/GenericTemplate.hs" #-}








{-# LINE 51 "templates/GenericTemplate.hs" #-}

{-# LINE 61 "templates/GenericTemplate.hs" #-}

{-# LINE 70 "templates/GenericTemplate.hs" #-}

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is (1), it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
	happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
	 (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action

{-# LINE 148 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Int ->                    -- token number
         Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let (i) = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k - ((1) :: Int)) sts of
	 sts1@(((st1@(HappyState (action))):(_))) ->
        	let r = fn stk in  -- it doesn't hurt to always seq here...
       		happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
        happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))
       where (sts1@(((st1@(HappyState (action))):(_)))) = happyDrop k ((st):(sts))
             drop_stk = happyDropStk k stk

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
       happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))
       where (sts1@(((st1@(HappyState (action))):(_)))) = happyDrop k ((st):(sts))
             drop_stk = happyDropStk k stk





             new_state = action


happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n - ((1) :: Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n - ((1)::Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction

{-# LINE 246 "templates/GenericTemplate.hs" #-}
happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery ((1) is the error token)

-- parse error if we are in recovery and we fail again
happyFail (1) tk old_st _ stk@(x `HappyStk` _) =
     let (i) = (case x of { HappyErrorToken (i) -> i }) in
--	trace "failing" $ 
        happyError_ i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  (1) tk old_st (((HappyState (action))):(sts)) 
						(saved_tok `HappyStk` _ `HappyStk` stk) =
--	trace ("discarding state, depth " ++ show (length stk))  $
	action (1) (1) tk (HappyState (action)) sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
	action (1) (1) tk (HappyState (action)) sts ( (HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--	happySeq = happyDoSeq
-- otherwise it emits
-- 	happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.

{-# LINE 312 "templates/GenericTemplate.hs" #-}
{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.

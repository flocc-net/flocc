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
module Compiler.Front.SrcParser ( parse, parseAndLabel ) where

import Compiler.Front.Indices ( Idx, IdxSet )
import Compiler.Front.ExprTree ( Expr(..), IdxTree(..), Val(..), initExprVarIds, renewExprIds )
import Compiler.Front.SrcLexer ( Token(..) )

import Control.Monad.State.Strict ( StateT )

-- parser produced by Happy Version 1.18.8

data HappyAbsSyn t4 t5 t6 t7 t8
	= HappyTerminal (Token)
	| HappyErrorToken Int
	| HappyAbsSyn4 t4
	| HappyAbsSyn5 t5
	| HappyAbsSyn6 t6
	| HappyAbsSyn7 t7
	| HappyAbsSyn8 t8

action_0 (9) = happyShift action_2
action_0 (11) = happyShift action_5
action_0 (14) = happyShift action_6
action_0 (19) = happyShift action_7
action_0 (21) = happyShift action_8
action_0 (23) = happyShift action_9
action_0 (24) = happyShift action_10
action_0 (25) = happyShift action_11
action_0 (26) = happyShift action_12
action_0 (27) = happyShift action_13
action_0 (28) = happyShift action_14
action_0 (4) = happyGoto action_3
action_0 (5) = happyGoto action_4
action_0 _ = happyFail

action_1 (9) = happyShift action_2
action_1 _ = happyFail

action_2 (18) = happyShift action_19
action_2 (19) = happyShift action_20
action_2 (23) = happyShift action_21
action_2 (7) = happyGoto action_24
action_2 _ = happyFail

action_3 (9) = happyShift action_2
action_3 (11) = happyShift action_5
action_3 (14) = happyShift action_6
action_3 (19) = happyShift action_7
action_3 (21) = happyShift action_8
action_3 (23) = happyShift action_9
action_3 (24) = happyShift action_10
action_3 (25) = happyShift action_11
action_3 (26) = happyShift action_12
action_3 (27) = happyShift action_13
action_3 (28) = happyShift action_14
action_3 (29) = happyAccept
action_3 (4) = happyGoto action_23
action_3 (5) = happyGoto action_4
action_3 _ = happyFail

action_4 _ = happyReduce_7

action_5 (9) = happyShift action_2
action_5 (11) = happyShift action_5
action_5 (14) = happyShift action_6
action_5 (19) = happyShift action_7
action_5 (21) = happyShift action_8
action_5 (23) = happyShift action_9
action_5 (24) = happyShift action_10
action_5 (25) = happyShift action_11
action_5 (26) = happyShift action_12
action_5 (27) = happyShift action_13
action_5 (28) = happyShift action_14
action_5 (4) = happyGoto action_22
action_5 (5) = happyGoto action_4
action_5 _ = happyFail

action_6 (18) = happyShift action_19
action_6 (19) = happyShift action_20
action_6 (23) = happyShift action_21
action_6 (7) = happyGoto action_18
action_6 _ = happyFail

action_7 (9) = happyShift action_2
action_7 (11) = happyShift action_5
action_7 (14) = happyShift action_6
action_7 (19) = happyShift action_7
action_7 (21) = happyShift action_8
action_7 (23) = happyShift action_9
action_7 (24) = happyShift action_10
action_7 (25) = happyShift action_11
action_7 (26) = happyShift action_12
action_7 (27) = happyShift action_13
action_7 (28) = happyShift action_14
action_7 (4) = happyGoto action_15
action_7 (5) = happyGoto action_4
action_7 (6) = happyGoto action_17
action_7 _ = happyReduce_14

action_8 (9) = happyShift action_2
action_8 (11) = happyShift action_5
action_8 (14) = happyShift action_6
action_8 (19) = happyShift action_7
action_8 (21) = happyShift action_8
action_8 (23) = happyShift action_9
action_8 (24) = happyShift action_10
action_8 (25) = happyShift action_11
action_8 (26) = happyShift action_12
action_8 (27) = happyShift action_13
action_8 (28) = happyShift action_14
action_8 (4) = happyGoto action_15
action_8 (5) = happyGoto action_4
action_8 (6) = happyGoto action_16
action_8 _ = happyReduce_14

action_9 _ = happyReduce_8

action_10 _ = happyReduce_9

action_11 _ = happyReduce_10

action_12 _ = happyReduce_11

action_13 _ = happyReduce_12

action_14 _ = happyReduce_13

action_15 (9) = happyShift action_2
action_15 (11) = happyShift action_5
action_15 (14) = happyShift action_6
action_15 (19) = happyShift action_7
action_15 (21) = happyShift action_8
action_15 (23) = happyShift action_9
action_15 (24) = happyShift action_10
action_15 (25) = happyShift action_11
action_15 (26) = happyShift action_12
action_15 (27) = happyShift action_13
action_15 (28) = happyShift action_14
action_15 (4) = happyGoto action_23
action_15 (5) = happyGoto action_4
action_15 _ = happyReduce_16

action_16 (17) = happyShift action_30
action_16 (22) = happyShift action_32
action_16 _ = happyFail

action_17 (17) = happyShift action_30
action_17 (20) = happyShift action_31
action_17 _ = happyFail

action_18 (15) = happyShift action_29
action_18 _ = happyFail

action_19 _ = happyReduce_17

action_20 (18) = happyShift action_19
action_20 (19) = happyShift action_20
action_20 (23) = happyShift action_21
action_20 (7) = happyGoto action_27
action_20 (8) = happyGoto action_28
action_20 _ = happyFail

action_21 _ = happyReduce_18

action_22 (9) = happyShift action_2
action_22 (11) = happyShift action_5
action_22 (12) = happyShift action_26
action_22 (14) = happyShift action_6
action_22 (19) = happyShift action_7
action_22 (21) = happyShift action_8
action_22 (23) = happyShift action_9
action_22 (24) = happyShift action_10
action_22 (25) = happyShift action_11
action_22 (26) = happyShift action_12
action_22 (27) = happyShift action_13
action_22 (28) = happyShift action_14
action_22 (4) = happyGoto action_23
action_22 (5) = happyGoto action_4
action_22 _ = happyFail

action_23 (9) = happyShift action_2
action_23 (11) = happyShift action_5
action_23 (14) = happyShift action_6
action_23 (19) = happyShift action_7
action_23 (21) = happyShift action_8
action_23 (23) = happyShift action_9
action_23 (24) = happyShift action_10
action_23 (25) = happyShift action_11
action_23 (26) = happyShift action_12
action_23 (27) = happyShift action_13
action_23 (28) = happyShift action_14
action_23 (4) = happyGoto action_23
action_23 (5) = happyGoto action_4
action_23 _ = happyReduce_6

action_24 (16) = happyShift action_25
action_24 _ = happyFail

action_25 (9) = happyShift action_2
action_25 (11) = happyShift action_5
action_25 (14) = happyShift action_6
action_25 (19) = happyShift action_7
action_25 (21) = happyShift action_8
action_25 (23) = happyShift action_9
action_25 (24) = happyShift action_10
action_25 (25) = happyShift action_11
action_25 (26) = happyShift action_12
action_25 (27) = happyShift action_13
action_25 (28) = happyShift action_14
action_25 (4) = happyGoto action_38
action_25 (5) = happyGoto action_4
action_25 _ = happyFail

action_26 (9) = happyShift action_2
action_26 (11) = happyShift action_5
action_26 (14) = happyShift action_6
action_26 (19) = happyShift action_7
action_26 (21) = happyShift action_8
action_26 (23) = happyShift action_9
action_26 (24) = happyShift action_10
action_26 (25) = happyShift action_11
action_26 (26) = happyShift action_12
action_26 (27) = happyShift action_13
action_26 (28) = happyShift action_14
action_26 (4) = happyGoto action_37
action_26 (5) = happyGoto action_4
action_26 _ = happyFail

action_27 _ = happyReduce_20

action_28 (17) = happyShift action_35
action_28 (20) = happyShift action_36
action_28 _ = happyFail

action_29 (9) = happyShift action_2
action_29 (11) = happyShift action_5
action_29 (14) = happyShift action_6
action_29 (19) = happyShift action_7
action_29 (21) = happyShift action_8
action_29 (23) = happyShift action_9
action_29 (24) = happyShift action_10
action_29 (25) = happyShift action_11
action_29 (26) = happyShift action_12
action_29 (27) = happyShift action_13
action_29 (28) = happyShift action_14
action_29 (4) = happyGoto action_34
action_29 (5) = happyGoto action_4
action_29 _ = happyFail

action_30 (9) = happyShift action_2
action_30 (11) = happyShift action_5
action_30 (14) = happyShift action_6
action_30 (19) = happyShift action_7
action_30 (21) = happyShift action_8
action_30 (23) = happyShift action_9
action_30 (24) = happyShift action_10
action_30 (25) = happyShift action_11
action_30 (26) = happyShift action_12
action_30 (27) = happyShift action_13
action_30 (28) = happyShift action_14
action_30 (4) = happyGoto action_33
action_30 (5) = happyGoto action_4
action_30 _ = happyFail

action_31 _ = happyReduce_2

action_32 _ = happyReduce_5

action_33 (9) = happyShift action_2
action_33 (11) = happyShift action_5
action_33 (14) = happyShift action_6
action_33 (19) = happyShift action_7
action_33 (21) = happyShift action_8
action_33 (23) = happyShift action_9
action_33 (24) = happyShift action_10
action_33 (25) = happyShift action_11
action_33 (26) = happyShift action_12
action_33 (27) = happyShift action_13
action_33 (28) = happyShift action_14
action_33 (4) = happyGoto action_23
action_33 (5) = happyGoto action_4
action_33 _ = happyReduce_15

action_34 (9) = happyShift action_2
action_34 (11) = happyShift action_5
action_34 (14) = happyShift action_6
action_34 (19) = happyShift action_7
action_34 (21) = happyShift action_8
action_34 (23) = happyShift action_9
action_34 (24) = happyShift action_10
action_34 (25) = happyShift action_11
action_34 (26) = happyShift action_12
action_34 (27) = happyShift action_13
action_34 (28) = happyShift action_14
action_34 (4) = happyGoto action_23
action_34 (5) = happyGoto action_4
action_34 _ = happyReduce_3

action_35 (18) = happyShift action_19
action_35 (19) = happyShift action_20
action_35 (23) = happyShift action_21
action_35 (7) = happyGoto action_41
action_35 _ = happyFail

action_36 _ = happyReduce_19

action_37 (9) = happyShift action_2
action_37 (11) = happyShift action_5
action_37 (13) = happyShift action_40
action_37 (14) = happyShift action_6
action_37 (19) = happyShift action_7
action_37 (21) = happyShift action_8
action_37 (23) = happyShift action_9
action_37 (24) = happyShift action_10
action_37 (25) = happyShift action_11
action_37 (26) = happyShift action_12
action_37 (27) = happyShift action_13
action_37 (28) = happyShift action_14
action_37 (4) = happyGoto action_23
action_37 (5) = happyGoto action_4
action_37 _ = happyFail

action_38 (9) = happyShift action_2
action_38 (10) = happyShift action_39
action_38 (11) = happyShift action_5
action_38 (14) = happyShift action_6
action_38 (19) = happyShift action_7
action_38 (21) = happyShift action_8
action_38 (23) = happyShift action_9
action_38 (24) = happyShift action_10
action_38 (25) = happyShift action_11
action_38 (26) = happyShift action_12
action_38 (27) = happyShift action_13
action_38 (28) = happyShift action_14
action_38 (4) = happyGoto action_23
action_38 (5) = happyGoto action_4
action_38 _ = happyFail

action_39 (9) = happyShift action_2
action_39 (11) = happyShift action_5
action_39 (14) = happyShift action_6
action_39 (19) = happyShift action_7
action_39 (21) = happyShift action_8
action_39 (23) = happyShift action_9
action_39 (24) = happyShift action_10
action_39 (25) = happyShift action_11
action_39 (26) = happyShift action_12
action_39 (27) = happyShift action_13
action_39 (28) = happyShift action_14
action_39 (4) = happyGoto action_43
action_39 (5) = happyGoto action_4
action_39 _ = happyFail

action_40 (9) = happyShift action_2
action_40 (11) = happyShift action_5
action_40 (14) = happyShift action_6
action_40 (19) = happyShift action_7
action_40 (21) = happyShift action_8
action_40 (23) = happyShift action_9
action_40 (24) = happyShift action_10
action_40 (25) = happyShift action_11
action_40 (26) = happyShift action_12
action_40 (27) = happyShift action_13
action_40 (28) = happyShift action_14
action_40 (4) = happyGoto action_42
action_40 (5) = happyGoto action_4
action_40 _ = happyFail

action_41 _ = happyReduce_21

action_42 (9) = happyShift action_2
action_42 (11) = happyShift action_5
action_42 (14) = happyShift action_6
action_42 (19) = happyShift action_7
action_42 (21) = happyShift action_8
action_42 (23) = happyShift action_9
action_42 (24) = happyShift action_10
action_42 (25) = happyShift action_11
action_42 (26) = happyShift action_12
action_42 (27) = happyShift action_13
action_42 (28) = happyShift action_14
action_42 (4) = happyGoto action_23
action_42 (5) = happyGoto action_4
action_42 _ = happyReduce_4

action_43 (9) = happyShift action_2
action_43 (11) = happyShift action_5
action_43 (14) = happyShift action_6
action_43 (19) = happyShift action_7
action_43 (21) = happyShift action_8
action_43 (23) = happyShift action_9
action_43 (24) = happyShift action_10
action_43 (25) = happyShift action_11
action_43 (26) = happyShift action_12
action_43 (27) = happyShift action_13
action_43 (28) = happyShift action_14
action_43 (4) = happyGoto action_23
action_43 (5) = happyGoto action_4
action_43 _ = happyReduce_1

happyReduce_1 = happyReduce 6 4 happyReduction_1
happyReduction_1 ((HappyAbsSyn4  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn7  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (Let defId happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_2 = happySpecReduce_3  4 happyReduction_2
happyReduction_2 _
	(HappyAbsSyn6  happy_var_2)
	_
	 =  HappyAbsSyn4
		 (Tup defId happy_var_2
	)
happyReduction_2 _ _ _  = notHappyAtAll 

happyReduce_3 = happyReduce 4 4 happyReduction_3
happyReduction_3 ((HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn7  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (Fun defId happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_4 = happyReduce 6 4 happyReduction_4
happyReduction_4 ((HappyAbsSyn4  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn4  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (If defId happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_5 = happySpecReduce_3  4 happyReduction_5
happyReduction_5 _
	(HappyAbsSyn6  happy_var_2)
	_
	 =  HappyAbsSyn4
		 (Rel defId happy_var_2
	)
happyReduction_5 _ _ _  = notHappyAtAll 

happyReduce_6 = happySpecReduce_2  4 happyReduction_6
happyReduction_6 (HappyAbsSyn4  happy_var_2)
	(HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn4
		 (App defId happy_var_1 happy_var_2
	)
happyReduction_6 _ _  = notHappyAtAll 

happyReduce_7 = happySpecReduce_1  4 happyReduction_7
happyReduction_7 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn4
		 (Lit defId happy_var_1
	)
happyReduction_7 _  = notHappyAtAll 

happyReduce_8 = happySpecReduce_1  4 happyReduction_8
happyReduction_8 (HappyTerminal (TokVar happy_var_1))
	 =  HappyAbsSyn4
		 (Var defId defId happy_var_1
	)
happyReduction_8 _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_1  5 happyReduction_9
happyReduction_9 (HappyTerminal (TokBool happy_var_1))
	 =  HappyAbsSyn5
		 (B happy_var_1
	)
happyReduction_9 _  = notHappyAtAll 

happyReduce_10 = happySpecReduce_1  5 happyReduction_10
happyReduction_10 (HappyTerminal (TokInt happy_var_1))
	 =  HappyAbsSyn5
		 (I happy_var_1
	)
happyReduction_10 _  = notHappyAtAll 

happyReduce_11 = happySpecReduce_1  5 happyReduction_11
happyReduction_11 (HappyTerminal (TokFloat happy_var_1))
	 =  HappyAbsSyn5
		 (F happy_var_1
	)
happyReduction_11 _  = notHappyAtAll 

happyReduce_12 = happySpecReduce_1  5 happyReduction_12
happyReduction_12 (HappyTerminal (TokString happy_var_1))
	 =  HappyAbsSyn5
		 (S happy_var_1
	)
happyReduction_12 _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_1  5 happyReduction_13
happyReduction_13 _
	 =  HappyAbsSyn5
		 (NullVal
	)

happyReduce_14 = happySpecReduce_0  6 happyReduction_14
happyReduction_14  =  HappyAbsSyn6
		 ([]
	)

happyReduce_15 = happySpecReduce_3  6 happyReduction_15
happyReduction_15 (HappyAbsSyn4  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn6
		 (happy_var_3 : happy_var_1
	)
happyReduction_15 _ _ _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_1  6 happyReduction_16
happyReduction_16 (HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn6
		 ([happy_var_1]
	)
happyReduction_16 _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_1  7 happyReduction_17
happyReduction_17 _
	 =  HappyAbsSyn7
		 (IdxNub defId
	)

happyReduce_18 = happySpecReduce_1  7 happyReduction_18
happyReduction_18 (HappyTerminal (TokVar happy_var_1))
	 =  HappyAbsSyn7
		 (IdxLeaf defId defId happy_var_1
	)
happyReduction_18 _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_3  7 happyReduction_19
happyReduction_19 _
	(HappyAbsSyn8  happy_var_2)
	_
	 =  HappyAbsSyn7
		 (IdxTup defId happy_var_2
	)
happyReduction_19 _ _ _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_1  8 happyReduction_20
happyReduction_20 (HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn8
		 ([happy_var_1]
	)
happyReduction_20 _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_3  8 happyReduction_21
happyReduction_21 (HappyAbsSyn7  happy_var_3)
	_
	(HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn8
		 (happy_var_3 : happy_var_1
	)
happyReduction_21 _ _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 29 29 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	TokLet -> cont 9;
	TokIn -> cont 10;
	TokIf -> cont 11;
	TokThen -> cont 12;
	TokElse -> cont 13;
	TokBSlash -> cont 14;
	TokArrow -> cont 15;
	TokEq -> cont 16;
	TokComma -> cont 17;
	TokUnderscore -> cont 18;
	TokLParen -> cont 19;
	TokRParen -> cont 20;
	TokLSqParen -> cont 21;
	TokRSqParen -> cont 22;
	TokVar happy_dollar_dollar -> cont 23;
	TokBool happy_dollar_dollar -> cont 24;
	TokInt happy_dollar_dollar -> cont 25;
	TokFloat happy_dollar_dollar -> cont 26;
	TokString happy_dollar_dollar -> cont 27;
	TokNull -> cont 28;
	_ -> happyError' (tk:tks)
	}

happyError_ 29 tk tks = happyError' tks
happyError_ _ tk tks = happyError' (tk:tks)

newtype HappyIdentity a = HappyIdentity a
happyIdentity = HappyIdentity
happyRunIdentity (HappyIdentity a) = a

instance Monad HappyIdentity where
    return = HappyIdentity
    (HappyIdentity p) >>= q = q p

happyThen :: () => HappyIdentity a -> (a -> HappyIdentity b) -> HappyIdentity b
happyThen = (>>=)
happyReturn :: () => a -> HappyIdentity a
happyReturn = (return)
happyThen1 m k tks = (>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> HappyIdentity a
happyReturn1 = \a tks -> (return) a
happyError' :: () => [(Token)] -> HappyIdentity a
happyError' = HappyIdentity . parseError

parseInternal tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


defId :: Idx
defId = -1

-- |Parse error function
parseError :: [Token] -> a
parseError tl = error $ "Parse error\n" ++ (show tl)

-- |Reverses idx tuple patterns to put them in the correct order as they were
-- |built using left recursion.
cleanUpIdxTrees :: IdxTree -> IdxTree
cleanUpIdxTrees it = case it of
  (IdxTup i l) -> IdxTup i (map cleanUpIdxTrees (reverse l))
  i -> i

-- |Converts tuples with no children to null vals, and expands out tuples
-- |with one child to be the child itself. Also reverses all lists of expressions
-- |to put them in the correct order as they were built using left recursion.
cleanUpTuples :: Expr -> Expr
cleanUpTuples exp = case exp of
  (Tup i [])         -> Lit i (NullVal)
  (Tup i (child:[])) -> cleanUpTuples child
  (Tup i l)          -> Tup i (map cleanUpTuples (reverse l))
  (Rel i l)          -> Rel i (map cleanUpTuples (reverse l))
  (Fun i it e)       -> Fun i (cleanUpIdxTrees it) (cleanUpTuples e)
  (App i fe ae)      -> App i (cleanUpTuples fe) (cleanUpTuples ae)
  (If i pe te ee)    -> If i (cleanUpTuples pe) (cleanUpTuples te) (cleanUpTuples ee)
  (Let i it be ie)   -> Let i (cleanUpIdxTrees it) (cleanUpTuples be) (cleanUpTuples ie)
  _                  -> exp
  

-- |Parse method to export as does some basic post processing
-- |using cleanUpTuples
parse :: [Token] -> Expr
parse tl = cleanUpTuples $ parseInternal tl

-- |Parse method that also creates unique ids for all expressions
-- |and for all variables
parseAndLabel :: Monad m => [(String, Idx)] -> [Token] -> StateT IdxSet m Expr
parseAndLabel env tl = do
  let expr = parse tl
  expr' <- renewExprIds expr
  expr'' <- initExprVarIds env expr'
  return expr''
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

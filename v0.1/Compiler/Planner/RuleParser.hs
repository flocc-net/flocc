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
module Compiler.Planner.RuleParser ( parseRuleSet, parseAndLabelRuleSet, 
  Rule, Level, RuleSet ) where

import Compiler.Front.Indices ( Idx, IdxSet )
import Compiler.Front.ExprTree ( Expr(..), IdxTree(..), Val(..), initExprVarIds, initIdxTreeExpIds, initIdxTreeVarIds, renewExprIds )
import Compiler.Planner.RuleLexer ( Token(..), PosnToken(..), scanRuleSet )

import Control.Monad.State.Strict ( StateT, mapM )

-- parser produced by Happy Version 1.18.8

data HappyAbsSyn t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14
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

action_0 (16) = happyShift action_2
action_0 (4) = happyGoto action_3
action_0 _ = happyFail

action_1 (16) = happyShift action_2
action_1 _ = happyFail

action_2 (35) = happyShift action_4
action_2 _ = happyFail

action_3 (41) = happyAccept
action_3 _ = happyFail

action_4 (5) = happyGoto action_5
action_4 _ = happyReduce_2

action_5 (15) = happyShift action_7
action_5 (6) = happyGoto action_6
action_5 _ = happyReduce_1

action_6 _ = happyReduce_3

action_7 (37) = happyShift action_8
action_7 _ = happyFail

action_8 (33) = happyShift action_9
action_8 _ = happyFail

action_9 (7) = happyGoto action_10
action_9 _ = happyReduce_5

action_10 (35) = happyShift action_12
action_10 (8) = happyGoto action_11
action_10 _ = happyReduce_4

action_11 _ = happyReduce_6

action_12 (15) = happyShift action_14
action_12 (16) = happyShift action_15
action_12 (27) = happyShift action_16
action_12 (28) = happyShift action_17
action_12 (35) = happyShift action_18
action_12 (13) = happyGoto action_13
action_12 _ = happyFail

action_13 (23) = happyShift action_21
action_13 _ = happyFail

action_14 _ = happyReduce_31

action_15 _ = happyReduce_30

action_16 _ = happyReduce_28

action_17 (15) = happyShift action_14
action_17 (16) = happyShift action_15
action_17 (27) = happyShift action_16
action_17 (28) = happyShift action_17
action_17 (35) = happyShift action_18
action_17 (13) = happyGoto action_19
action_17 (14) = happyGoto action_20
action_17 _ = happyFail

action_18 _ = happyReduce_29

action_19 _ = happyReduce_33

action_20 (26) = happyShift action_38
action_20 (29) = happyShift action_39
action_20 _ = happyFail

action_21 (15) = happyShift action_25
action_21 (16) = happyShift action_26
action_21 (17) = happyShift action_27
action_21 (19) = happyShift action_28
action_21 (22) = happyShift action_29
action_21 (28) = happyShift action_30
action_21 (30) = happyShift action_31
action_21 (35) = happyShift action_32
action_21 (36) = happyShift action_33
action_21 (37) = happyShift action_34
action_21 (38) = happyShift action_35
action_21 (39) = happyShift action_36
action_21 (40) = happyShift action_37
action_21 (9) = happyGoto action_22
action_21 (10) = happyGoto action_23
action_21 (11) = happyGoto action_24
action_21 _ = happyFail

action_22 (32) = happyShift action_48
action_22 (34) = happyShift action_49
action_22 _ = happyFail

action_23 (15) = happyShift action_25
action_23 (16) = happyShift action_26
action_23 (17) = happyShift action_27
action_23 (19) = happyShift action_28
action_23 (22) = happyShift action_29
action_23 (28) = happyShift action_30
action_23 (30) = happyShift action_31
action_23 (35) = happyShift action_32
action_23 (36) = happyShift action_33
action_23 (37) = happyShift action_34
action_23 (38) = happyShift action_35
action_23 (39) = happyShift action_36
action_23 (40) = happyShift action_37
action_23 (10) = happyGoto action_47
action_23 (11) = happyGoto action_24
action_23 _ = happyReduce_8

action_24 _ = happyReduce_16

action_25 _ = happyReduce_19

action_26 _ = happyReduce_18

action_27 (15) = happyShift action_14
action_27 (16) = happyShift action_15
action_27 (27) = happyShift action_16
action_27 (28) = happyShift action_17
action_27 (35) = happyShift action_18
action_27 (13) = happyGoto action_46
action_27 _ = happyFail

action_28 (15) = happyShift action_25
action_28 (16) = happyShift action_26
action_28 (17) = happyShift action_27
action_28 (19) = happyShift action_28
action_28 (22) = happyShift action_29
action_28 (28) = happyShift action_30
action_28 (30) = happyShift action_31
action_28 (35) = happyShift action_32
action_28 (36) = happyShift action_33
action_28 (37) = happyShift action_34
action_28 (38) = happyShift action_35
action_28 (39) = happyShift action_36
action_28 (40) = happyShift action_37
action_28 (10) = happyGoto action_45
action_28 (11) = happyGoto action_24
action_28 _ = happyFail

action_29 (15) = happyShift action_14
action_29 (16) = happyShift action_15
action_29 (27) = happyShift action_16
action_29 (28) = happyShift action_17
action_29 (35) = happyShift action_18
action_29 (13) = happyGoto action_44
action_29 _ = happyFail

action_30 (15) = happyShift action_25
action_30 (16) = happyShift action_26
action_30 (17) = happyShift action_27
action_30 (19) = happyShift action_28
action_30 (22) = happyShift action_29
action_30 (28) = happyShift action_30
action_30 (30) = happyShift action_31
action_30 (35) = happyShift action_32
action_30 (36) = happyShift action_33
action_30 (37) = happyShift action_34
action_30 (38) = happyShift action_35
action_30 (39) = happyShift action_36
action_30 (40) = happyShift action_37
action_30 (10) = happyGoto action_41
action_30 (11) = happyGoto action_24
action_30 (12) = happyGoto action_43
action_30 _ = happyReduce_25

action_31 (15) = happyShift action_25
action_31 (16) = happyShift action_26
action_31 (17) = happyShift action_27
action_31 (19) = happyShift action_28
action_31 (22) = happyShift action_29
action_31 (28) = happyShift action_30
action_31 (30) = happyShift action_31
action_31 (35) = happyShift action_32
action_31 (36) = happyShift action_33
action_31 (37) = happyShift action_34
action_31 (38) = happyShift action_35
action_31 (39) = happyShift action_36
action_31 (40) = happyShift action_37
action_31 (10) = happyGoto action_41
action_31 (11) = happyGoto action_24
action_31 (12) = happyGoto action_42
action_31 _ = happyReduce_25

action_32 _ = happyReduce_17

action_33 _ = happyReduce_20

action_34 _ = happyReduce_21

action_35 _ = happyReduce_22

action_36 _ = happyReduce_23

action_37 _ = happyReduce_24

action_38 (15) = happyShift action_14
action_38 (16) = happyShift action_15
action_38 (27) = happyShift action_16
action_38 (28) = happyShift action_17
action_38 (35) = happyShift action_18
action_38 (13) = happyGoto action_40
action_38 _ = happyFail

action_39 _ = happyReduce_32

action_40 _ = happyReduce_34

action_41 (15) = happyShift action_25
action_41 (16) = happyShift action_26
action_41 (17) = happyShift action_27
action_41 (19) = happyShift action_28
action_41 (22) = happyShift action_29
action_41 (28) = happyShift action_30
action_41 (30) = happyShift action_31
action_41 (35) = happyShift action_32
action_41 (36) = happyShift action_33
action_41 (37) = happyShift action_34
action_41 (38) = happyShift action_35
action_41 (39) = happyShift action_36
action_41 (40) = happyShift action_37
action_41 (10) = happyGoto action_47
action_41 (11) = happyGoto action_24
action_41 _ = happyReduce_27

action_42 (26) = happyShift action_54
action_42 (31) = happyShift action_56
action_42 _ = happyFail

action_43 (26) = happyShift action_54
action_43 (29) = happyShift action_55
action_43 _ = happyFail

action_44 (24) = happyShift action_53
action_44 _ = happyFail

action_45 (15) = happyShift action_25
action_45 (16) = happyShift action_26
action_45 (17) = happyShift action_27
action_45 (19) = happyShift action_28
action_45 (20) = happyShift action_52
action_45 (22) = happyShift action_29
action_45 (28) = happyShift action_30
action_45 (30) = happyShift action_31
action_45 (35) = happyShift action_32
action_45 (36) = happyShift action_33
action_45 (37) = happyShift action_34
action_45 (38) = happyShift action_35
action_45 (39) = happyShift action_36
action_45 (40) = happyShift action_37
action_45 (10) = happyGoto action_47
action_45 (11) = happyGoto action_24
action_45 _ = happyFail

action_46 (25) = happyShift action_51
action_46 _ = happyFail

action_47 (15) = happyShift action_25
action_47 (16) = happyShift action_26
action_47 (17) = happyShift action_27
action_47 (19) = happyShift action_28
action_47 (22) = happyShift action_29
action_47 (28) = happyShift action_30
action_47 (30) = happyShift action_31
action_47 (35) = happyShift action_32
action_47 (36) = happyShift action_33
action_47 (37) = happyShift action_34
action_47 (38) = happyShift action_35
action_47 (39) = happyShift action_36
action_47 (40) = happyShift action_37
action_47 (10) = happyGoto action_47
action_47 (11) = happyGoto action_24
action_47 _ = happyReduce_15

action_48 (15) = happyShift action_25
action_48 (16) = happyShift action_26
action_48 (17) = happyShift action_27
action_48 (19) = happyShift action_28
action_48 (22) = happyShift action_29
action_48 (28) = happyShift action_30
action_48 (30) = happyShift action_31
action_48 (35) = happyShift action_32
action_48 (36) = happyShift action_33
action_48 (37) = happyShift action_34
action_48 (38) = happyShift action_35
action_48 (39) = happyShift action_36
action_48 (40) = happyShift action_37
action_48 (10) = happyGoto action_50
action_48 (11) = happyGoto action_24
action_48 _ = happyFail

action_49 _ = happyReduce_7

action_50 (15) = happyShift action_25
action_50 (16) = happyShift action_26
action_50 (17) = happyShift action_27
action_50 (19) = happyShift action_28
action_50 (22) = happyShift action_29
action_50 (28) = happyShift action_30
action_50 (30) = happyShift action_31
action_50 (35) = happyShift action_32
action_50 (36) = happyShift action_33
action_50 (37) = happyShift action_34
action_50 (38) = happyShift action_35
action_50 (39) = happyShift action_36
action_50 (40) = happyShift action_37
action_50 (10) = happyGoto action_47
action_50 (11) = happyGoto action_24
action_50 _ = happyReduce_9

action_51 (15) = happyShift action_25
action_51 (16) = happyShift action_26
action_51 (17) = happyShift action_27
action_51 (19) = happyShift action_28
action_51 (22) = happyShift action_29
action_51 (28) = happyShift action_30
action_51 (30) = happyShift action_31
action_51 (35) = happyShift action_32
action_51 (36) = happyShift action_33
action_51 (37) = happyShift action_34
action_51 (38) = happyShift action_35
action_51 (39) = happyShift action_36
action_51 (40) = happyShift action_37
action_51 (10) = happyGoto action_60
action_51 (11) = happyGoto action_24
action_51 _ = happyFail

action_52 (15) = happyShift action_25
action_52 (16) = happyShift action_26
action_52 (17) = happyShift action_27
action_52 (19) = happyShift action_28
action_52 (22) = happyShift action_29
action_52 (28) = happyShift action_30
action_52 (30) = happyShift action_31
action_52 (35) = happyShift action_32
action_52 (36) = happyShift action_33
action_52 (37) = happyShift action_34
action_52 (38) = happyShift action_35
action_52 (39) = happyShift action_36
action_52 (40) = happyShift action_37
action_52 (10) = happyGoto action_59
action_52 (11) = happyGoto action_24
action_52 _ = happyFail

action_53 (15) = happyShift action_25
action_53 (16) = happyShift action_26
action_53 (17) = happyShift action_27
action_53 (19) = happyShift action_28
action_53 (22) = happyShift action_29
action_53 (28) = happyShift action_30
action_53 (30) = happyShift action_31
action_53 (35) = happyShift action_32
action_53 (36) = happyShift action_33
action_53 (37) = happyShift action_34
action_53 (38) = happyShift action_35
action_53 (39) = happyShift action_36
action_53 (40) = happyShift action_37
action_53 (10) = happyGoto action_58
action_53 (11) = happyGoto action_24
action_53 _ = happyFail

action_54 (15) = happyShift action_25
action_54 (16) = happyShift action_26
action_54 (17) = happyShift action_27
action_54 (19) = happyShift action_28
action_54 (22) = happyShift action_29
action_54 (28) = happyShift action_30
action_54 (30) = happyShift action_31
action_54 (35) = happyShift action_32
action_54 (36) = happyShift action_33
action_54 (37) = happyShift action_34
action_54 (38) = happyShift action_35
action_54 (39) = happyShift action_36
action_54 (40) = happyShift action_37
action_54 (10) = happyGoto action_57
action_54 (11) = happyGoto action_24
action_54 _ = happyFail

action_55 _ = happyReduce_11

action_56 _ = happyReduce_14

action_57 (15) = happyShift action_25
action_57 (16) = happyShift action_26
action_57 (17) = happyShift action_27
action_57 (19) = happyShift action_28
action_57 (22) = happyShift action_29
action_57 (28) = happyShift action_30
action_57 (30) = happyShift action_31
action_57 (35) = happyShift action_32
action_57 (36) = happyShift action_33
action_57 (37) = happyShift action_34
action_57 (38) = happyShift action_35
action_57 (39) = happyShift action_36
action_57 (40) = happyShift action_37
action_57 (10) = happyGoto action_47
action_57 (11) = happyGoto action_24
action_57 _ = happyReduce_26

action_58 (15) = happyShift action_25
action_58 (16) = happyShift action_26
action_58 (17) = happyShift action_27
action_58 (19) = happyShift action_28
action_58 (22) = happyShift action_29
action_58 (28) = happyShift action_30
action_58 (30) = happyShift action_31
action_58 (35) = happyShift action_32
action_58 (36) = happyShift action_33
action_58 (37) = happyShift action_34
action_58 (38) = happyShift action_35
action_58 (39) = happyShift action_36
action_58 (40) = happyShift action_37
action_58 (10) = happyGoto action_47
action_58 (11) = happyGoto action_24
action_58 _ = happyReduce_12

action_59 (15) = happyShift action_25
action_59 (16) = happyShift action_26
action_59 (17) = happyShift action_27
action_59 (19) = happyShift action_28
action_59 (21) = happyShift action_62
action_59 (22) = happyShift action_29
action_59 (28) = happyShift action_30
action_59 (30) = happyShift action_31
action_59 (35) = happyShift action_32
action_59 (36) = happyShift action_33
action_59 (37) = happyShift action_34
action_59 (38) = happyShift action_35
action_59 (39) = happyShift action_36
action_59 (40) = happyShift action_37
action_59 (10) = happyGoto action_47
action_59 (11) = happyGoto action_24
action_59 _ = happyFail

action_60 (15) = happyShift action_25
action_60 (16) = happyShift action_26
action_60 (17) = happyShift action_27
action_60 (18) = happyShift action_61
action_60 (19) = happyShift action_28
action_60 (22) = happyShift action_29
action_60 (28) = happyShift action_30
action_60 (30) = happyShift action_31
action_60 (35) = happyShift action_32
action_60 (36) = happyShift action_33
action_60 (37) = happyShift action_34
action_60 (38) = happyShift action_35
action_60 (39) = happyShift action_36
action_60 (40) = happyShift action_37
action_60 (10) = happyGoto action_47
action_60 (11) = happyGoto action_24
action_60 _ = happyFail

action_61 (15) = happyShift action_25
action_61 (16) = happyShift action_26
action_61 (17) = happyShift action_27
action_61 (19) = happyShift action_28
action_61 (22) = happyShift action_29
action_61 (28) = happyShift action_30
action_61 (30) = happyShift action_31
action_61 (35) = happyShift action_32
action_61 (36) = happyShift action_33
action_61 (37) = happyShift action_34
action_61 (38) = happyShift action_35
action_61 (39) = happyShift action_36
action_61 (40) = happyShift action_37
action_61 (10) = happyGoto action_64
action_61 (11) = happyGoto action_24
action_61 _ = happyFail

action_62 (15) = happyShift action_25
action_62 (16) = happyShift action_26
action_62 (17) = happyShift action_27
action_62 (19) = happyShift action_28
action_62 (22) = happyShift action_29
action_62 (28) = happyShift action_30
action_62 (30) = happyShift action_31
action_62 (35) = happyShift action_32
action_62 (36) = happyShift action_33
action_62 (37) = happyShift action_34
action_62 (38) = happyShift action_35
action_62 (39) = happyShift action_36
action_62 (40) = happyShift action_37
action_62 (10) = happyGoto action_63
action_62 (11) = happyGoto action_24
action_62 _ = happyFail

action_63 (15) = happyShift action_25
action_63 (16) = happyShift action_26
action_63 (17) = happyShift action_27
action_63 (19) = happyShift action_28
action_63 (22) = happyShift action_29
action_63 (28) = happyShift action_30
action_63 (30) = happyShift action_31
action_63 (35) = happyShift action_32
action_63 (36) = happyShift action_33
action_63 (37) = happyShift action_34
action_63 (38) = happyShift action_35
action_63 (39) = happyShift action_36
action_63 (40) = happyShift action_37
action_63 (10) = happyGoto action_47
action_63 (11) = happyGoto action_24
action_63 _ = happyReduce_13

action_64 (15) = happyShift action_25
action_64 (16) = happyShift action_26
action_64 (17) = happyShift action_27
action_64 (19) = happyShift action_28
action_64 (22) = happyShift action_29
action_64 (28) = happyShift action_30
action_64 (30) = happyShift action_31
action_64 (35) = happyShift action_32
action_64 (36) = happyShift action_33
action_64 (37) = happyShift action_34
action_64 (38) = happyShift action_35
action_64 (39) = happyShift action_36
action_64 (40) = happyShift action_37
action_64 (10) = happyGoto action_47
action_64 (11) = happyGoto action_24
action_64 _ = happyReduce_10

happyReduce_1 = happySpecReduce_3  4 happyReduction_1
happyReduction_1 (HappyAbsSyn5  happy_var_3)
	(HappyTerminal (PosnTok _ _ _ (TokVar happy_var_2)))
	_
	 =  HappyAbsSyn4
		 ((happy_var_2, reverse happy_var_3)
	)
happyReduction_1 _ _ _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_0  5 happyReduction_2
happyReduction_2  =  HappyAbsSyn5
		 ([]
	)

happyReduce_3 = happySpecReduce_2  5 happyReduction_3
happyReduction_3 (HappyAbsSyn6  happy_var_2)
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn5
		 (happy_var_2 : happy_var_1
	)
happyReduction_3 _ _  = notHappyAtAll 

happyReduce_4 = happyReduce 4 6 happyReduction_4
happyReduction_4 ((HappyAbsSyn7  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (PosnTok _ _ _ (TokInt happy_var_2))) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 ((happy_var_2, reverse happy_var_4)
	) `HappyStk` happyRest

happyReduce_5 = happySpecReduce_0  7 happyReduction_5
happyReduction_5  =  HappyAbsSyn7
		 ([]
	)

happyReduce_6 = happySpecReduce_2  7 happyReduction_6
happyReduction_6 (HappyAbsSyn8  happy_var_2)
	(HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn7
		 (happy_var_2 : happy_var_1
	)
happyReduction_6 _ _  = notHappyAtAll 

happyReduce_7 = happyReduce 5 8 happyReduction_7
happyReduction_7 (_ `HappyStk`
	(HappyAbsSyn9  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn13  happy_var_2) `HappyStk`
	(HappyTerminal (PosnTok _ _ _ (TokVar happy_var_1))) `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 ((happy_var_1, happy_var_2, reverse happy_var_4)
	) `HappyStk` happyRest

happyReduce_8 = happySpecReduce_1  9 happyReduction_8
happyReduction_8 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn9
		 ([happy_var_1]
	)
happyReduction_8 _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_3  9 happyReduction_9
happyReduction_9 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn9
		 (happy_var_3 : happy_var_1
	)
happyReduction_9 _ _ _  = notHappyAtAll 

happyReduce_10 = happyReduce 6 10 happyReduction_10
happyReduction_10 ((HappyAbsSyn10  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn13  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (Let defId happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_11 = happySpecReduce_3  10 happyReduction_11
happyReduction_11 _
	(HappyAbsSyn12  happy_var_2)
	_
	 =  HappyAbsSyn10
		 (cleanUpTuple (reverse happy_var_2)
	)
happyReduction_11 _ _ _  = notHappyAtAll 

happyReduce_12 = happyReduce 4 10 happyReduction_12
happyReduction_12 ((HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn13  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (Fun defId happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_13 = happyReduce 6 10 happyReduction_13
happyReduction_13 ((HappyAbsSyn10  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn10  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (If defId happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_14 = happySpecReduce_3  10 happyReduction_14
happyReduction_14 _
	(HappyAbsSyn12  happy_var_2)
	_
	 =  HappyAbsSyn10
		 (Rel defId (reverse happy_var_2)
	)
happyReduction_14 _ _ _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_2  10 happyReduction_15
happyReduction_15 (HappyAbsSyn10  happy_var_2)
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (App defId happy_var_1 happy_var_2
	)
happyReduction_15 _ _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_1  10 happyReduction_16
happyReduction_16 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn10
		 (Lit defId happy_var_1
	)
happyReduction_16 _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_1  10 happyReduction_17
happyReduction_17 (HappyTerminal (PosnTok _ _ _ (TokVar happy_var_1)))
	 =  HappyAbsSyn10
		 (Var defId defId happy_var_1
	)
happyReduction_17 _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_1  10 happyReduction_18
happyReduction_18 _
	 =  HappyAbsSyn10
		 (Var defId defId "ruleset"
	)

happyReduce_19 = happySpecReduce_1  10 happyReduction_19
happyReduction_19 _
	 =  HappyAbsSyn10
		 (Var defId defId "level"
	)

happyReduce_20 = happySpecReduce_1  11 happyReduction_20
happyReduction_20 (HappyTerminal (PosnTok _ _ _ (TokBool happy_var_1)))
	 =  HappyAbsSyn11
		 (B happy_var_1
	)
happyReduction_20 _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_1  11 happyReduction_21
happyReduction_21 (HappyTerminal (PosnTok _ _ _ (TokInt happy_var_1)))
	 =  HappyAbsSyn11
		 (I happy_var_1
	)
happyReduction_21 _  = notHappyAtAll 

happyReduce_22 = happySpecReduce_1  11 happyReduction_22
happyReduction_22 (HappyTerminal (PosnTok _ _ _ (TokFloat happy_var_1)))
	 =  HappyAbsSyn11
		 (F happy_var_1
	)
happyReduction_22 _  = notHappyAtAll 

happyReduce_23 = happySpecReduce_1  11 happyReduction_23
happyReduction_23 (HappyTerminal (PosnTok _ _ _ (TokString happy_var_1)))
	 =  HappyAbsSyn11
		 (S happy_var_1
	)
happyReduction_23 _  = notHappyAtAll 

happyReduce_24 = happySpecReduce_1  11 happyReduction_24
happyReduction_24 _
	 =  HappyAbsSyn11
		 (NullVal
	)

happyReduce_25 = happySpecReduce_0  12 happyReduction_25
happyReduction_25  =  HappyAbsSyn12
		 ([]
	)

happyReduce_26 = happySpecReduce_3  12 happyReduction_26
happyReduction_26 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn12
		 (happy_var_3 : happy_var_1
	)
happyReduction_26 _ _ _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_1  12 happyReduction_27
happyReduction_27 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn12
		 ([happy_var_1]
	)
happyReduction_27 _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_1  13 happyReduction_28
happyReduction_28 _
	 =  HappyAbsSyn13
		 (IdxNub defId
	)

happyReduce_29 = happySpecReduce_1  13 happyReduction_29
happyReduction_29 (HappyTerminal (PosnTok _ _ _ (TokVar happy_var_1)))
	 =  HappyAbsSyn13
		 (IdxLeaf defId defId happy_var_1
	)
happyReduction_29 _  = notHappyAtAll 

happyReduce_30 = happySpecReduce_1  13 happyReduction_30
happyReduction_30 _
	 =  HappyAbsSyn13
		 (IdxLeaf defId defId "ruleset"
	)

happyReduce_31 = happySpecReduce_1  13 happyReduction_31
happyReduction_31 _
	 =  HappyAbsSyn13
		 (IdxLeaf defId defId "level"
	)

happyReduce_32 = happySpecReduce_3  13 happyReduction_32
happyReduction_32 _
	(HappyAbsSyn14  happy_var_2)
	_
	 =  HappyAbsSyn13
		 (IdxTup defId (reverse happy_var_2)
	)
happyReduction_32 _ _ _  = notHappyAtAll 

happyReduce_33 = happySpecReduce_1  14 happyReduction_33
happyReduction_33 (HappyAbsSyn13  happy_var_1)
	 =  HappyAbsSyn14
		 ([happy_var_1]
	)
happyReduction_33 _  = notHappyAtAll 

happyReduce_34 = happySpecReduce_3  14 happyReduction_34
happyReduction_34 (HappyAbsSyn13  happy_var_3)
	_
	(HappyAbsSyn14  happy_var_1)
	 =  HappyAbsSyn14
		 (happy_var_3 : happy_var_1
	)
happyReduction_34 _ _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 41 41 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	PosnTok _ _ _ TokLevel -> cont 15;
	PosnTok _ _ _ TokRuleset -> cont 16;
	PosnTok _ _ _ TokLet -> cont 17;
	PosnTok _ _ _ TokIn -> cont 18;
	PosnTok _ _ _ TokIf -> cont 19;
	PosnTok _ _ _ TokThen -> cont 20;
	PosnTok _ _ _ TokElse -> cont 21;
	PosnTok _ _ _ TokBSlash -> cont 22;
	PosnTok _ _ _ TokImplies -> cont 23;
	PosnTok _ _ _ TokArrow -> cont 24;
	PosnTok _ _ _ TokEq -> cont 25;
	PosnTok _ _ _ TokComma -> cont 26;
	PosnTok _ _ _ TokUnderscore -> cont 27;
	PosnTok _ _ _ TokLParen -> cont 28;
	PosnTok _ _ _ TokRParen -> cont 29;
	PosnTok _ _ _ TokLSqParen -> cont 30;
	PosnTok _ _ _ TokRSqParen -> cont 31;
	PosnTok _ _ _ TokBar -> cont 32;
	PosnTok _ _ _ TokColon -> cont 33;
	PosnTok _ _ _ TokSemiColon -> cont 34;
	PosnTok _ _ _ (TokVar happy_dollar_dollar) -> cont 35;
	PosnTok _ _ _ (TokBool happy_dollar_dollar) -> cont 36;
	PosnTok _ _ _ (TokInt happy_dollar_dollar) -> cont 37;
	PosnTok _ _ _ (TokFloat happy_dollar_dollar) -> cont 38;
	PosnTok _ _ _ (TokString happy_dollar_dollar) -> cont 39;
	PosnTok _ _ _ TokNull -> cont 40;
	_ -> happyError' (tk:tks)
	}

happyError_ 41 tk tks = happyError' tks
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
happyError' :: () => [(PosnToken)] -> HappyIdentity a
happyError' = HappyIdentity . parseError

parseInternal tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


defId :: Idx
defId = -1

-- |Parse error function
parseError :: [PosnToken] -> a
parseError ((PosnTok _ lineNum colNum _):tl) = error $ "Rule file parse error on line " ++ (show lineNum)
  ++ ":" ++ (show colNum) ++ " near '"++ (concat $ map show $ take 10 tl) ++ "'"

-- |Converts tuples with no children to null vals, and expands out tuples
-- |with one child to be the child itself.
cleanUpTuple :: [Expr] -> Expr
cleanUpTuple exp = case exp of
  []           -> Lit defId (NullVal)
  (child:[])   -> child
  l            -> Tup defId l

-- |Labels the expression with expression ids and var ids
labelExpr :: Monad m => [(String, Idx)] -> Expr -> StateT IdxSet m Expr
labelExpr env expr = do
  expr' <- renewExprIds expr
  expr'' <- initExprVarIds env expr'
  return expr''

-- |A set of possible expansions for a function application
type Rule = (String, IdxTree, [Expr])

labelRule :: Monad m => 
  [(String, Idx)] -> 
  Rule -> StateT IdxSet m Rule
labelRule env (name,idpat,exprs) = do
  idpat' <- initIdxTreeExpIds idpat
  (idpat'', env') <- initIdxTreeVarIds idpat'
  exprs' <- mapM (labelExpr (env' ++ env)) exprs
  return (name,idpat'',exprs')

-- |A set of expansion rules for a particular nesting level
type Level = (Int, [Rule])

labelLevel ::  Monad m => 
  [(String, Idx)] -> 
  Level -> StateT IdxSet m Level
labelLevel env (levelNum, rules) = do
  rules' <- mapM (labelRule env) rules
  return (levelNum, rules')

-- |A set of rules for each nesting level of the architecture
type RuleSet = (String, [Level])

-- |Parse method to export. Takes a list of tokens and returns a rule set.
parseRuleSet :: [PosnToken] -> RuleSet
parseRuleSet = parseInternal

-- |Parse method that also creates unique ids for all expressions
-- |and for all variables
{-parseAndLabelRuleSet :: Monad m => [(String, Idx)] -> [PosnToken] -> StateT IdxSet m RuleSet
parseAndLabelRuleSet env tl = do
  let (ruleSetName, levelList) = parseRuleSet tl
  levelList' <- mapM (labelLevel env) levelList
  return (ruleSetName, levelList')
-}
parseAndLabelRuleSet :: Monad m => [(String, Idx)] -> String -> StateT IdxSet m RuleSet
parseAndLabelRuleSet env s = do 
  let tl = scanRuleSet s
  let (ruleSetName, levelList) = parseRuleSet tl
  levelList' <- mapM (labelLevel env) levelList
  return (ruleSetName, levelList')
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

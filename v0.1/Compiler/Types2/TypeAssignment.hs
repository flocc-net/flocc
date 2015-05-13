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
module Compiler.Types2.TypeAssignment ( 
  assignTypes, assignNewTypes, --globalTypeTerms, 
  typeOfVal, intTy, ExpLbl(..), FuncTerm, FuncEnv, FuncConstr, FuncScheme,
  TyToken(..), TyTerm, TyConstr, TyEnv, TyScheme, TySchemeEx,
  showExprWithTypes, showGlobalTypeTerms, showTyScheme,
  rel, relNonOrd, getTupleAccessorFun,
  typeSchemesToTerms, stripConstrLabels,
  nullTy, boolTy, floatTy, typeName,
  findDefaultSubsts ) where

-- Assigns most general types to expressions in the language

import Compiler.Types2.TermLanguage
import Compiler.Types2.TermBuilder

import Compiler.Front.ExprTree (Expr(Lit, If, Rel), Val(..), showExprTree)
import Compiler.Front.Indices (IdxSet, Idx)
import Compiler.Front.Common (delimList, lookupAssocOrValue, ShowP(..))
--import GlobalEnv (resolveGlobalNamesInEnv)

import Data.Map.Strict (Map, fromList, unions)
import qualified Data.Map.Strict as Data.Map (lookup, map, insert, toList, empty, difference, fromList)
import Data.Foldable (foldlM)
import Data.Functor.Identity (runIdentity)
import Debug.Trace (trace)

import Control.Monad.State.Strict ( StateT, lift, modify, execStateT )

-- |Token type for type term language
data TyToken = 
     Ty String
--    TyNull
--  | TyEvery
--  | TyBool
--  | TyInt
--  | TyFloat
--  | TyString
--  | TyRel
--  | TyOrdered
--  | TyNonOrdered
  deriving (Eq, Show, Read, Ord)

instance ShowP TyToken where
  showP tok = show tok

type TyTerm = FuncTerm TyToken -- Term (FunctionToken TyToken)
type TyScheme = FuncScheme TyToken --Scheme (FunctionToken TyToken)
type TySchemeEx = SchemeEx ExpLbl (FunctionToken TyToken)
type TyConstr = FuncConstr TyToken -- Constr TyTerm
type TyEnv = FuncEnv TyToken -- TermEnv (FunctionToken TyToken)

stripConstrLabels :: TyConstr -> TyConstr
stripConstrLabels (a :=: b) = (stripTermLabelsRec a :=: stripTermLabelsRec b)

-- |typeName takes a type and returns the type name.
typeName :: TyTerm -> Maybe String
typeName (Term (Tok (Ty name)) _) = Just name
typeName (LTerm _ (Tok (Ty name)) _) = Just name
typeName other = Nothing

-- |typeSchemeToTerm takes a type scheme and returns the term
-- |if there are no bound variables in it, or raises an error otherwise
typeSchemeToTerm :: TyScheme -> TyTerm
typeSchemeToTerm s = case s of
  Scheme [] t -> t
  Scheme l  _ -> error $ "typeSchemeToTerm: polymorphic scheme found: " ++ (show s)

-- |typeSchemesToTermsassignNewTypes transforms a map of type schemes, to type terms
-- |but raises an error if any polymorphic type schemes remain.
typeSchemesToTerms :: Map Idx TyScheme -> Map Idx TyTerm 
typeSchemesToTerms sMap = Data.Map.map typeSchemeToTerm sMap

-- |Pretty print type term
showTyTerm :: TyTerm -> String
showTyTerm t = case t of 
--  (Term (Tok TyNull) _)   -> "Null"
--  (Term (Tok TyEvery) _)  -> "Every"
--  (Term (Tok TyBool) _)   -> "Bool"
--  (Term (Tok TyInt) _)    -> "Int"
--  (Term (Tok TyFloat) _)  -> "Float"
--  (Term (Tok TyString) _) -> "String"
--  (Term (Tok TyRel) l) -> "[" ++ (delimList " " $ map showTyTerm l) ++ "]"
  (Term (Tok (Ty s)) []) -> s
  (Term (Tok (Ty s)) l)  -> "(" ++ s ++ " " ++ (delimList " " $ map showTyTerm l) ++ ")"
  (Term FunTok (a:b:_)) -> "(" ++ (showTyTerm a) ++ " -> " ++ (showTyTerm b) ++ ")"
  (Term TupTok l) -> "(" ++ (delimList ", " $ map  showTyTerm l) ++ ")"
  (LTerm lbls (Tok (Ty s)) []) -> s ++ (showPLabels lbls)
  (LTerm lbls (Tok (Ty s)) l)  -> "(" ++ s ++ " " ++ (delimList " " $ map showTyTerm l) ++ ")" ++ (showLabels lbls)
  (LTerm lbls FunTok (a:b:_)) -> "(" ++ (showTyTerm a) ++ " -> " ++ (showTyTerm b) ++ ")" ++ (showLabels lbls)
  (LTerm lbls TupTok l) -> "(" ++ (delimList ", " $ map  showTyTerm l) ++ ")" ++ (showLabels lbls)
  _ -> (showP t)

-- |Pretty print type scheme
showTyScheme :: TyScheme -> String
showTyScheme (Scheme [] term) = showTyTerm term
showTyScheme (Scheme vars term) = "forall " ++ 
  (delimList "," $ map (\i -> ("v" ++ show i)) vars) ++
  " => " ++ (showTyTerm term)

showExprTy :: TyEnv -> Idx -> String
showExprTy env idx = case lookupTermMaybe env idx of
  Just v  -> " :: " ++ (showTyScheme v)
  Nothing -> " :: ERROR: no type term exists in env with idx " ++ (show idx) 

showExprWithTypes :: TyEnv -> Expr -> String
showExprWithTypes env exp = showExprTree env showExprTy 2 exp

-- |namedTy takes a string and list of child types
-- |and returns the type term for it.
namedTy :: String -> [TyTerm] -> TyTerm
namedTy n l = Term (Tok (Ty n)) l

-- |The first var is the value term, and the second is the structure term
rel :: TyTerm -> TyTerm -> TyTerm
rel a b = Term (Tok (Ty "Rel")) [a, b]
--rel a b = Term (Tok TyRel) [a, b]

--relOrd = (Term (Tok TyOrdered) [])
relOrd = (Term (Tok (Ty "Ordered")) [])
--relNonOrd = (Term (Tok TyNonOrdered) [])
relNonOrd = (Term (Tok (Ty "NonOrdered")) [])

--intTy = (Term (Tok TyInt) [])
intTy = (Term (Tok (Ty "Int")) [])
--floatTy = (Term (Tok TyFloat) [])
floatTy = (Term (Tok (Ty "Float")) [])
--nullTy = (Term (Tok TyNull) [])
nullTy = (Term (Tok (Ty "Null")) [])
--everyTy = (Term (Tok TyEvery) [])
everyTy = (Term (Tok (Ty "Every")) [])
--stringTy = (Term (Tok TyString) [])
stringTy = (Term (Tok (Ty "String")) [])
--boolTy = (Term (Tok TyBool) [])
boolTy = (Term (Tok (Ty "Bool")) [])

binaryOp :: TyTerm -> TyTerm
binaryOp x = fun (tup [x, x]) x

binaryOpScheme :: TyTerm -> TyScheme
binaryOpScheme x = scm [] $ binaryOp x

intBinOpNames = ["addi","subi","muli","divi"]

floatBinOpNames = ["addf","subf","mulf","divf"]

binaryBoolScheme :: TyTerm -> TyScheme
binaryBoolScheme x = scm [] $ fun (tup [x, x]) boolTy

intCmpOpNames = ["eqi", "neqi", "gti", "gtei", "lti", "ltei"]

floatCmpOpNames = ["eqf", "neqf", "gtf", "gtef", "ltf", "ltef"]

boolBinOpNames = ["and", "or", "xor", "implies", "equiv"]

binaryOps = 
  (map (\n -> (n, binaryOpScheme intTy)) intBinOpNames) ++ 
  (map (\n -> (n, binaryOpScheme floatTy)) floatBinOpNames) ++
  (map (\n -> (n, binaryBoolScheme intTy)) intCmpOpNames) ++
  (map (\n -> (n, binaryBoolScheme floatTy)) floatCmpOpNames) ++
  (map (\n -> (n, binaryBoolScheme boolTy)) boolBinOpNames) ++
  [("not", scm [] $ fun boolTy boolTy)]

-- |tupleOffsetFunctions are the function names of
-- |functions that take a tuple and return the ith member
tupleOffsetFunctions :: [[String]]
tupleOffsetFunctions = [
    [],             -- no such thing as 1ary tuples
    ["fst", "snd"] -- of pairs
  ] ++ [ [ "tup" ++ (show tupOffset) ++ "of" ++ (show tupSize) 
          | tupOffset <- [1..tupSize] ] 
            | tupSize <- [3..12] ]

-- |tupleOffsetFunMap is a map from (tupSize,tupOffset) pairs
-- |to the names of the tuple accessor functions
tupleOffsetFunMap :: Map (Int,Int) String
tupleOffsetFunMap = Data.Map.fromList $ concat $ l'
  where l' = [ [ ((tupSize,tupOffset),funName) 
                 | (tupOffset,funName) <- zip [1..] funList ] 
                   | (tupSize,funList) <- zip [1..] tupleOffsetFunctions ] 

-- |getTupleAccessorFun takes the tuple size and tuple length
-- |and returns the function-name and var id of the tuple
-- |accessor function.
getTupleAccessorFun :: Int -> Int -> (String, Idx)
getTupleAccessorFun sz off = case Data.Map.lookup (sz,off) tupleOffsetFunMap of
  Just name -> error "Need to code getVid part of tuple accessor funcs"--(name, -1)
  Nothing   -> error $ "There is no tuple accessor function for " ++ (show sz) ++ "," ++ (show off)

-- |makeTupleOffsetFunType makes the type scheme for a tuple 
-- |accessor function who's tuple size is the first argument
-- |and offset is the second.
makeTupleOffsetFunType :: Int -> Int -> TyScheme
makeTupleOffsetFunType sz off = Scheme [1..sz] (fun (tup inTypes) (Var off))
  where inTypes = map Var [1..sz]

-- |tupleOffsetFunctionTypes are the type schemes of all the 
-- |tuple accessor functions
tupleOffsetFunctionTypes = concat
  [ [ (funName, makeTupleOffsetFunType tupSize tupOffset  ) 
      | (tupOffset,funName) <- zip [1..] funList ]
        | (tupSize,funList) <- zip [1..] tupleOffsetFunctions ]

varEnv = binaryOps ++ tupleOffsetFunctionTypes ++ [
  ("id", scm [vara] $ fun vara vara),
  ("eq", scm [vara] $ fun (tup [vara, vara]) boolTy),
  ("map", scm [vara, varb, varc, vard, vare] $
          fun (tup [fun (vara) (varc), fun (tup [vara, varb]) (vard)]) 
              (fun (rel (tup [vara, varb]) (vare)) (rel (tup [varc, vard]) (vare)))),
  -- for now both inputs of a join must have same ordering...
  ("ejoin", scm [vara, varb, varc, vard, vare, varf] $ 
            fun (tup [fun (tup [vara, varb]) (vare), 
                      fun (tup [varc, vard]) (vare)]) 
              (fun (tup [rel (tup [vara, varb]) (varf), 
                         rel (tup [varc, vard]) (varf)]) 
                   (rel (tup [tup [vara, varc], tup [varb, vard]]) (varf)))),
  ("greduce", scm [vara, varb, varc, vard, vare] $ 
              fun (tup [fun (tup [vara, varb]) (varc), 
                        fun (tup [vara, varb]) (vard), 
                        binaryOp vard]) 
                (fun (rel (tup [vara, varb]) (vare)) (rel (tup [varc, vard]) (relNonOrd)))),
  ("genmatrix", scm [] $
                fun (intTy) (rel (tup [tup [intTy, intTy], floatTy]) (relNonOrd))),
  ("everyval", scm [] $ 
               fun (nullTy) (everyTy)),
  ("filter", scm [vara, varb] $ 
             fun (fun (vara) (boolTy)) (
                 fun (rel vara varb) (rel vara varb))),
  ("split", scm [vara, varb] $ 
             fun (fun (vara) (boolTy)) (
                 fun (rel vara varb) (tup [rel vara varb, rel vara varb]))),
  ("union", scm [] $
            fun (tup [rel vara varb, rel vara varb]) (rel vara varb)),
  ("intersect", scm [] $
            fun (tup [rel vara varb, rel vara varb]) (rel vara varb)),
  ("except", scm [] $
            fun (tup [rel vara varb, rel vara varb]) (rel vara varb))
  ]

--globalTypeTerms :: TyEnv
--globalTypeTerms = resolveGlobalNamesInEnv varEnv

-- |Handy pretty printer to help make sense of the global dependence term environment
showGlobalTypeTerms :: String
showGlobalTypeTerms = delimList "\n" $ map (\(k,v) -> (k ++ " :: " ++ showTyScheme v)) varEnv

-- |Returns the type of a literal value
typeOfVal :: Val -> TyTerm
typeOfVal (S _) = stringTy
typeOfVal (I _) = intTy
typeOfVal (B _) = boolTy
typeOfVal (F _) = floatTy
typeOfVal (NullVal) = nullTy

-- |defaultTypes is a list of default type values for 
-- |various members of compound types.
defaultTypes :: [((String, Int), TyTerm)]
defaultTypes = [
    (("Dict", 2), namedTy "NoIdx" []),
    (("Dict", 3), namedTy "NoOrd" []),
    (("Dict", 4), namedTy "OnePass" []),
    (("DivDict", 2), namedTy "DefPartFun" [])
  ]

-- |findDefaultsVisitor examines types to find any type variables that should
-- |be replaced with default types.
findDefaultsVisitor :: Monad m => String -> (Int, TyTerm) -> StateT (Map Idx (String, Int)) m ()
findDefaultsVisitor tyName (offset, term) = case term of
  (Var idx) -> do
    modify (\s -> Data.Map.insert idx (tyName, offset) s)
    return ()
  (LVar _ idx) -> do
    modify (\s -> Data.Map.insert idx (tyName, offset) s)
    return ()
  (Term (Tok (Ty name)) l) -> do
    mapM (findDefaultsVisitor name) $ zip [0..] l
    return () 
  (LTerm _ (Tok (Ty name)) l) -> do
    mapM (findDefaultsVisitor name) $ zip [0..] l
    return () 
  (Term TupTok l) -> do
    mapM (findDefaultsVisitor "randomnonsense") $ zip [0..] l
    return ()
  (LTerm _ TupTok l) -> do
    mapM (findDefaultsVisitor "randomnonsense") $ zip [0..] l
    return ()
  (Term FunTok l) -> do
    mapM (findDefaultsVisitor "randomnonsense") $ zip [0..] l
    return ()
  (LTerm _ FunTok l) -> do
    mapM (findDefaultsVisitor "randomnonsense") $ zip [0..] l
    return ()
  other -> do return ()

-- |findDefaults looks through a type environment and finds any
-- |unbound type vars that remain, for which a default may be
-- |defined.
findDefaults :: TyEnv -> Map Idx (String, Int)
findDefaults env = unions outs2 
  where ins = map (\(_, Scheme l t) -> (Data.Map.fromList $ zip l (repeat ()), t)) env 
        outs = map (\(vars, term) -> (vars, runIdentity $ execStateT (findDefaultsVisitor "randomnonsense" (-1, term)) Data.Map.empty)) ins
        outs2 = map (\(vars, defvars) -> defvars `Data.Map.difference` vars) outs
  

-- |findDefaultSubsts takes some type terms and returns a list of 
-- |substitutions for those type vars that should be replaced with default values.
findDefaultSubsts :: TyEnv -> Substs TyTerm 
findDefaultSubsts env = subs
  where defs = findDefaults env
        subs = map (\(vid, nameOffset) -> 
                  Var vid :|-> (lookupAssocOrValue (error $ "TyAssignment:findDefaultSubsts: no default type for " ++ (show nameOffset)) 
                                nameOffset defaultTypes)) $ Data.Map.toList defs

-- |Build initial term environment for types
buildForExpr :: Monad a => TyEnv -> Expr -> StateT (TyEnv) (StateT (IdxSet) a) ([TyConstr], TyTerm)
buildForExpr varEnv exp = case exp of
  -- type of the literal
  (Lit i vl) -> do
    let ty = labelTerm (ProdLbl i) $ typeOfVal vl
    bindTermInState (Scheme [] ty) i
    return ([], ty)
  -- relation expression
  (Rel i l) -> case l of
    -- empty list: just a term var
    [] -> do
      v <- lift $ newTermVarFromState
      let v' = labelTerm (ProdLbl i) v
      bindTermInState (Scheme [] v') i
      return ([], v')
    -- non empty list: all children same type
    _  -> do
      l' <- mapM (\e -> buildTermsForExpr varEnv e buildForExpr) l
      let (cl,tl) = unzip l'
      let (headTy:tail) = tl
      let cl' = map (\ty -> headTy :=: ty) tail
      let ty = labelTerm (ProdLbl i) $ rel headTy (relNonOrd)
      bindTermInState (Scheme [] ty) i -- TODO: change so not just non ord
      return (cl' ++ (concat cl), ty)
  -- if expression
  (If i pe te ee) -> do
    v <- lift $ newTermVarFromState
    let v' = labelTerm (ProdLbl i) v
    bindTermInState (Scheme [] v') i
    (c1,t1) <- buildTermsForExpr varEnv pe buildForExpr
    (c2,t2) <- buildTermsForExpr varEnv te buildForExpr
    (c3,t3) <- buildTermsForExpr varEnv ee buildForExpr
    return ((v :=: t2):(v :=: t3):(t1 :=: boolTy):(c1 ++ c2 ++ c3), v')
  -- invoke term builder helper function
  _ -> buildTermsForExpr varEnv exp buildForExpr

-- |Takes an initial (global) type environment, and an expression
-- |and returns a type environment mapping all expression ids to
-- |type terms.
assignTypes :: Monad a => TyEnv -> Expr -> StateT (IdxSet) a TyEnv
assignTypes varEnv exp = do
  ret <- runTermInferencer inferTypes varEnv exp
  case ret of
    Left env -> return env
    Right constr -> error $ "Type assignment failed at constraint " ++ (show constr)
--  ret <- performConstraintAnalysis buildForExpr varEnv exp
--  case ret of 
--    Left env -> return env
--    Right constr -> error $ "Type assignment failed on constraint " ++ (show constr)

-- |Inferences types of an expression (unifying as it goes)
inferTypes :: Monad m => InferenceFunction TyToken m
inferTypes varEnv expr = case expr of
  -- literal expression
  (Lit i vl) -> do 
    let ty = labelTerm (ProdLbl i) $ typeOfVal vl
    bindTermInState (Scheme [] ty) i
    return ([], ty)
  -- conditional expression
  (If i pe te ee) -> do
    (s1, t1) <- inferTypes varEnv pe
    case unifyConstraints [t1 :=: boolTy] emptyTermEnv of
      (Left s1_1) -> do
        let s1l = s1_1 `composeSubsts` s1
        (s2, t2) <- inferTypes (applySubstsToEnv s1l varEnv) te
        let s2l = s2 `composeSubsts` s1l
        (s3, t3) <- inferTypes (applySubstsToEnv s2l varEnv) ee
        let s3l = s3 `composeSubsts` s2l
        -- TODO: confused about what subs need to be applied to what, when
        case unifyConstraints [t2 :=: t3] emptyTermEnv of
          (Left s4) -> do
             let term = labelTerm (ProdLbl i) $ applySubstsToTerm s4 t3
             bindTermInState (Scheme [] term) i
             return (s4 `composeSubsts` s3l, term)
          (Right failCon) -> error $ "Term inference failed on " ++ (show failCon)
      (Right failCon) -> error $ "If predicate of non boolean type " ++ (show pe) 
                                 ++ " :: " ++ (showTyTerm t1)
  -- relation expression
  (Rel i l) -> do
    -- process list insisting they all equate
    (_,sl,tl) <- foldlM (inferEqTermsFoldF inferTypes) (varEnv, nullSubsts, []) l
    case tl of 
      -- we know the type
      (t1:_) -> case t1 of
        (Term TupTok (keyT:valT:[]))    -> do
          let term = labelTerm (ProdLbl i) $ rel keyT valT
          bindTermInState (Scheme [] term) i
          return (sl, term)
        other -> error $ "Invalid relation key/value type pair " ++ (show other) 
      -- we don't know the type
      []     -> do 
        keyT <- lift $ newTermVarFromState
        valT <- lift $ newTermVarFromState
        let term = labelTerm (ProdLbl i) $ rel keyT valT
        bindTermInState (Scheme [] term) i
        return (sl, term)
  -- other expressions
  _ -> inferTerms inferTypes varEnv expr

-- |assignNewTypes takes the global type environment, a type environment giving type
-- |assignments for some of the sub expressions, and an expression and returns 
-- |a type environment mapping expression ids to type schemes.
assignNewTypes :: Monad a => TyEnv -> TyEnv -> Expr -> StateT (IdxSet) a TyEnv
assignNewTypes varEnv exprTypes expr = do
  ret <- runNewTermInferencer inferNewTypes varEnv exprTypes expr
  case ret of
    Left env -> return env
    Right constr -> error $ "Type assignment failed at constraint " ++ (show constr)

-- |Inferences types of an expression (unifying as it goes)
inferNewTypes :: Monad m => InferenceFunction TyToken m
inferNewTypes varEnv expr = case expr of
  -- literal expression
  (Lit i vl) -> do 
    let ty = labelTerm (ProdLbl i) $ typeOfVal vl
    bindTermInState (Scheme [] ty) i
    return ([], ty)
  -- conditional expression
  (If i pe te ee) -> do
    (s1, t1) <- (inferNewTerms inferNewTypes) varEnv pe
    case unifyConstraints [t1 :=: boolTy] emptyTermEnv of
      (Left s1_1) -> do
        let s1l = s1_1 `composeSubsts` s1
        (s2, t2) <- (inferNewTerms inferNewTypes) (applySubstsToEnv s1l varEnv) te
        let s2l = s2 `composeSubsts` s1l
        (s3, t3) <- (inferNewTerms inferNewTypes) (applySubstsToEnv s2l varEnv) ee
        let s3l = s3 `composeSubsts` s2l
        -- TODO: confused about what subs need to be applied to what, when
        case unifyConstraints [t2 :=: t3] emptyTermEnv of
          (Left s4) -> do
             let term = labelTerm (ProdLbl i) $ applySubstsToTerm s4 t3
             bindTermInState (Scheme [] term) i
             return (s4 `composeSubsts` s3l, term)
          (Right failCon) -> error $ "Term inference failed on " ++ (show failCon)
      (Right failCon) -> error $ "If predicate of non boolean type " ++ (show pe) 
                                 ++ " :: " ++ (showTyTerm t1)
  -- relation expression
  (Rel i l) -> do
    -- process list insisting they all equate
    (_,sl,tl) <- foldlM (inferEqTermsFoldF (inferNewTerms inferNewTypes)) (varEnv, nullSubsts, []) l
    case tl of 
      -- we know the type
      (t1:_) -> case t1 of
        (Term TupTok (keyT:valT:[]))    -> do
          let term = labelTerm (ProdLbl i) $ rel keyT valT
          bindTermInState (Scheme [] term) i
          return (sl, term)
        other -> error $ "Invalid relation key/value type pair " ++ (show other) 
      -- we don't know the type
      []     -> do 
        keyT <- lift $ newTermVarFromState
        valT <- lift $ newTermVarFromState
        let term = labelTerm (ProdLbl i) $ rel keyT valT
        bindTermInState (Scheme [] term) i
        return (sl, term)
  -- other expressions
  _ -> inferTerms (inferNewTerms inferNewTypes) varEnv expr



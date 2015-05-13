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
module Compiler.Back.Generators where

import Compiler.Back.Graph
import Compiler.Back.GenDecls
import Compiler.Back.Gen
import Compiler.Back.StrTemplates
import Compiler.Back.TypeNames

import Data.List (intersperse, intercalate)
import Data.Maybe (catMaybes, fromMaybe)
import Control.Monad.State.Strict (gets)
import Data.Foldable (foldrM, foldlM)
import Data.Functor.Identity (runIdentity)
import Data.Text (pack, unpack, replace)
import qualified Data.Map as DM
import Control.Monad.Catch

type SimpGenerator m = [Val m] -> Val m

simpGen :: (Monad m, MonadCatch m) => SimpGenerator m -> [Val m] -> GenM1 m (Val m)
simpGen f arg = do
  let result = f arg
  return result

gerr :: (Monad m, MonadCatch m) => String -> Generator m 
gerr gname val = do
  debug <- gets genDebugOut
  nid <- gets genCurrentNode
  error $ "Generator " ++ gname ++ " error\nFrom node: " ++ (show nid) ++ "\nVals: " ++ (show val) ++ "\nTrace: " ++ debug

genErrorC msg = do
  genError msg
  return $ CodeV ""

-- SHOW(TY)
-- ----------------

g1 :: (Monad m, MonadCatch m) => Generator m
g1 [TyV ty] = return (CodeV $ show ty)
g1 val = gerr "showType" val

-- DECLARE(VAR) // also declares structs if required
-- ----------------------------------------------------

toMaybeIdxName :: (Int, Maybe Id) -> Maybe (Int, Id) 
toMaybeIdxName (idx, mn) = case mn of
  Just n  -> Just (idx,n)
  Nothing -> Nothing


-- |generates a new struct declaration for a tuple type
decStruct :: (Monad m, MonadCatch m) => Id -> [Ty] -> GenM1 m Code
decStruct strName memList = do
    -- get type names for all members (with index offsets)
    names <- mapM genTypeName memList
    let idxNames = map toMaybeIdxName $ zip [treeIndexBase..] names
    let idxNames' = catMaybes idxNames
    -- generate functions
    ltFun <- genStructLT strName (Tup memList)
    eqFun <- genStructEq strName (Tup memList)
    eqStruct <- genEqStruct strName (Tup memList)
    hashFun <- genHashFun strName idxNames'
    printFun <- genStructPrint strName (Tup memList)
    emptyVal <- genStructEmpty strName names
    -- generate and return code
    let strCode  = "typedef struct " ++ strName ++ " {\n" ++ 
               (concat $ map (\(vid,tid) -> tid ++ " v" ++ (show vid) ++ ";\n") $ idxNames') ++
               ltFun ++ eqFun ++
               "} " ++ strName ++ ";\n" ++
               printFun++
               hashFun++
               eqStruct++
               emptyVal++
               "\n\n"
    return strCode

-- |genStructPrint structName type. Generates a printVal method for
-- |the struct.
genStructEmpty :: (Monad m, MonadCatch m) => Id -> [Maybe Id] -> GenM1 m Code
genStructEmpty strName tyNames = do
  -- generate method 
  let tyNames' = catMaybes tyNames
  let vals = intercalate ", " $ map (\tn -> "flocc::" ++ tn ++ "Empty") tyNames'
  let code1 = strName ++ " " ++ strName ++ "Empty = {" ++ vals ++ "};\n"
  -- return it
  return $ "namespace flocc {\n" ++ code1 ++ "\n}\n" 

-- |generates a new collection declaration  
decCollection :: (Monad m, MonadCatch m) => Id -> GenM m
decCollection className = do
  -- check if has already been declared
  let key =  (Lf $ IdOV className)
  beenDeclared <- getGlobal "classesDeclared" key
  case beenDeclared of
    -- if not
    Nothing -> do
      -- declare it 
      let eqFun = genCollectionEqMethod className
      output "decls" eqFun
      -- mark as declared
      setGlobal "classesDeclared" key (Just $ BoolV True)
    Just _ -> return ()


-- |genTypeName ty. Returns the type name for ty.
-- |Tuple type names are created by generating struct declarations for them
-- |and then saving their names in globals.
genTypeName :: (Monad m, MonadCatch m) => Ty -> GenM1 m (Maybe Id)
genTypeName ty = case ty of
  -- base types
  Lf lty -> case lty of
    -- scalar types
    _ | ty == intTy   -> return $ Just "int"
    _ | ty == uintTy  -> return $ Just "unsigned int"
    _ | ty == floatTy -> return $ Just "double"
    _ | ty == boolTy  -> return $ Just "bool"
    _ | ty == strTy   -> return $ Just "std::string"
    _ | ty == nullTy  -> return $ Nothing
    -- types carrying functions
    FunTy _ -> return Nothing
    -- structs with embedded functions
    LfTy "FunClass" [Lf (LfTy name [])] -> return $ Just $ "flocc::" ++ name
    -- collection types
    ListTy t -> do
      et <- genTypeName t
      case et of
        Just etN -> do 
          let cName = "std::list<" ++ etN ++ ">"
          decCollection cName
          return $ Just cName
        Nothing  -> error $ "genTypeName: you can't have a list of nulls!"
    OMapTy kt vt -> do
      kty <- genTypeName kt
      vty <- genTypeName vt
      case (kty, vty) of
        (Just ktn, vtn) -> do
          let cName = "std::map<" ++ ktn ++ ", " ++ (fromMaybe "nullStruct" vtn) ++ ">"
          decCollection cName
          return $ Just cName
        other -> error $ "genTypeName:OMap:you can't have an OMap with null keys!"
    HMapTy kt vt -> do
      kty <- genTypeName kt
      vty <- genTypeName vt
      case (kty, vty) of
        (Just ktn, vtn) -> do
          let cName = "std::unordered_map<" ++ ktn ++ ", " ++ (fromMaybe "nullStruct" vtn) ++ ">"
          decCollection cName
          return $ Just cName
        other -> error $ "genTypeName:OMap:you can't have an OMap with null keys!"
    -- distributed map
    (LfTy "DMap" [(Lf (LfTy mode [])), kt, vt, sf, pf, pd, md]) -> case mode of
      "Stm" -> error $ "Generators:genTypeName:can't create type for a DMap stream: " ++ (show ty)  
      "Vec" -> do
         -- declare proj function, for the vecmap secondary key
         let (Lf (FunTy ordFun)) = sf
         (ordDomTy :-> ordRanTy) <- getGraphTy ordFun
         projFunTy <- genStaticFun ordFun (Just $ Tup [kt, vt]) Nothing "inline static"
         -- use to get the right storage type
         let outTy = LfTy "SPtr" [Lf $ LfTy "VecMap" [Tup [kt, vt], kt, ordRanTy, projFunTy]]
         genTypeName $ Lf outTy
      "Hsh" -> do
         -- translate to local hashmap
         let outTy = lfTy "LMap" [lfTy "Hsh" [], kt, vt, sf]
         genTypeName outTy
    -- typeOf operator
    (LfTy "TypeOf" [Lf (LfTy varName [])]) -> return $ Just $ "TYPEOF(" ++ varName ++ ")" 
    -- all other lf types
    LfTy name l -> do
      l' <- mapM genTypeName l
      tn <- getTypeName lty l'
      return tn
    VarTy name -> return Nothing
    other -> error $ "gen:typeName:1 can't generate type name for " ++ (show ty)
  -- structs for tuples
  Tup l -> do
    -- try and look up from globals
    maybeId <- getGlobal "tupleStructNames" (Lf $ TyOV ty)
    case maybeId of
      Just (IdV sid) -> return $ Just sid
      Nothing  -> do
        -- if doesn't exist create a new name
        sidx <- newInt
        let sid = "struct" ++ (show sidx)
        -- generate the struct and output to declarations
        decCode <- decStruct sid l
        output "decls" decCode
        -- and save the name to globals
        setGlobal "tupleStructNames" (Lf $ TyOV ty) (Just $ IdV sid)
        return (Just sid)
  other -> error $ "gen:typeName:2 can't generate type name for " ++ (show other)

-- |genTyName [VarV ty var]. Returns the target name of the
-- |variable's type, or error if can't generate name.
genTyName :: (Monad m, MonadCatch m) => Generator m
genTyName [TyV ty] = do
  tyName <- genTypeName ty
  case tyName of
    Just name -> return $ IdV name
    Nothing -> return $ IdV "char"
genTyName [VarV ty var] = do
  tyName <- genTypeName ty
  case tyName of
    Just name -> return $ IdV name
    Nothing -> return $ IdV "char"
    --Nothing -> error $ "genTyName: can't generate type name for " ++ 
                    --   (show $ VarV ty var)

genMPITyName :: (Monad m, MonadCatch m) => Generator m
genMPITyName [inVar@(VarV ty (Lf idv)), tyVar@(VarV _ (Lf outidv))] = do
  mbTn <- getMPITypeName ty (Just idv)
  case mbTn of 
    Just (tyName, initCode) -> do
      -- init output var with mpi type
      num <- newInt
      let vname = "mpiTyTy"++(show num)
      varExp vname "" tyName mpiTyTy
      vid <- getLocalVal vname
      runGen "assignVar" ("assign"++vname) [tyVar, vid]
      -- return mpi type init/declaration code
      return $ CodeV $ initCode ++ ("<assign"++vname++">") ++ "\n"
    Nothing -> error $ "genMPITyName: can't generate type name for " ++ (show inVar)

-- |treeVarsToVar v. If v is a tree of 
treeVarsToVar :: (Monad m, MonadCatch m) => Val m -> Val m
treeVarsToVar (TreeV (Lf v)) = treeVarsToVar v
treeVarsToVar (TreeV (Tup l)) = VarV (Tup tl) (Tup vl)
  where l' = map (treeVarsToVar . TreeV) l
        (tl,vl) = unzip $ map (\(VarV t v) -> (t,v)) l'
treeVarsToVar (VarV t v) = (VarV t v)
treeVarsToVar (LitV NulVal) = LitV NulVal
treeVarsToVar other = error $ "gen:treeVarsToVar: can't handle " ++ (show other)

-- |decStructVar [VarV ty var]. Declares a struct var for type ty, named var.
-- |var must be a leaf id, and if the struct for ty hasn't yet been declared
-- |it is automatically.
decStructVar :: (Monad m, MonadCatch m) => Generator m
decStructVar arg@[VarV ty var, valTree] = case var of
  Lf vid -> do
    tyName <- genTypeName ty
    case tyName of
      -- declare the var
      Just tname -> case treeVarsToVar valTree of
        -- nothing to init with
        LitV NulVal   -> do
          -- get default initializer
          defInitExp <- defaultInitializer ty tname
          return (CodeV $ tname ++ " " ++ vid ++ (if defInitExp /= "" then "(" ++ defInitExp ++ ")" else "") ++ ";\n")
       {- -- init to value by assigning, if types are same
        VarV ty2 var2 | ty == ty2 -> do
          (CodeV initCode) <- assignVarGen [VarV ty var, VarV ty2 var2]
          return (CodeV $ tname ++ " " ++ vid ++ ";\n" ++ initCode)-}
        --  init to value by calling constructor, if types are different
        VarV ty2 var2 -> case (ty2, var2) of
          (Tup tl, Tup vl) | length tl == length vl -> do
            let vl' = map (treeLeaf $ "gen:decStructVar: init var vals can only be a leaf or a flat tuple of leaves:\n" ++ (show arg)) vl
            return (CodeV $ tname ++ " " ++ vid ++ "(" ++ (concat $ intersperse ", " vl') ++ ");\n")
          (_, Lf v) -> return (CodeV $ tname ++ " " ++ vid ++ "(" ++ v ++ ");\n")
      -- if it is a null var, don't declare it 
      Nothing -> return (CodeV "")
  other -> error $ "gen:decStructVar: can't declare a struct var with an id tree. must be a leaf!\n" ++ (show var)
decStructVar val = gerr "decStructVar" val

-- |decVar [VarV ty var, val]. Generates code to declare var with type ty, 
-- |and val passed to its constructor, unless val is LitV NulVal, in which 
-- |case the constructor is not called.
decInitVar :: (Monad m, MonadCatch m) => Generator m
decInitVar [invar@(VarV ty var), val] = case var of
  -- declare this single id
  Lf vid -> decStructVar [VarV ty var, val]
  -- break down var into separate ids
  Tup idL  -> case ty of
    Tup tyL | length idL == length tyL -> 
      -- break down the init val(s) for the separate ids
      case tidyVal val of
        -- no init vals
        LitV NulVal                -> do
          assL <- mapM (\(t,vid) -> do (CodeV c) <- decInitVar [VarV t vid, LitV NulVal]; return c) $ zip tyL idL
          return $ CodeV $ concat assL
        -- a tuple of vals 
        TreeV (Tup valL) | length valL == length idL -> do
          assL <- mapM (\(t,vid,v) -> do (CodeV c) <- decInitVar [VarV t vid, TreeV v]; return c) $ zip3 tyL idL valL
          return $ CodeV $ concat assL
        -- a tuple var that is the right size for the ids
        VarV (Tup tyL2) (Tup valL) | (length valL == length tyL2) && (length valL == length idL) -> do
          let vl = map (\(t,v) -> VarV t v) $ zip tyL2 valL
          assL <- mapM (\(t,vid,v) -> do (CodeV c) <- decInitVar [VarV t vid, v]; return c) $ zip3 tyL idL vl
          return $ CodeV $ concat assL
        -- other
        other -> error $ "gen:decVar: invalid initialization tuple " ++ (show val) ++ " for var " ++ (show invar) ++ ".\n"
    -- type doesnt match id list 
    other -> do
      genErrorC $ "gen:decVar: type doesn't match id list: " ++ (show idL) ++ " != " ++ (show ty)
  -- invalid var  
  other  -> do 
    genErrorC $ "gen:decVar: can't declare var " ++ (show var) ++ " with type " ++ (show ty) 
decInitVar val = gerr "decVar" val

-- |decInitVar [VarV ty var]. Returns code to initialize the 
decVar :: (Monad m, MonadCatch m) => Generator m
decVar [VarV ty var] = decInitVar [VarV ty var, LitV NulVal]

-- |initVar [VarV ty var, ]. Assigns a new value to a variable, by calling the 
-- |constructor again.
initVar :: (Monad m, MonadCatch m) => Generator m
initVar arg@[VarV ty var, valTree] = case var of
  Lf vid -> do
    tyName <- genTypeName ty
    case tyName of
      -- init the var
      Just tname -> case treeVarsToVar valTree of
        -- nothing to init with
        LitV NulVal   -> return (CodeV $ "// initVar " ++ vid ++ " :: " ++ tname ++ " with null.\n")
        -- init to value by assigning, if types are same
        VarV ty2 var2 | ty == ty2 -> do
          (CodeV initCode) <- assignVarGen [VarV ty var, VarV ty2 var2]
          return (CodeV $ initCode)
        --  init to value by calling constructor, if types are different
        VarV ty2 var2 -> case (ty2, var2) of
          (Tup tl, Tup vl) | length tl == length vl -> do
            let vl' = map (treeLeaf $ "gen:initVar: init var vals can only be a leaf or a flat tuple of leaves:\n" ++ (show arg)) vl
            return (CodeV $ vid ++ " = " ++ tname ++ "(" ++ (concat $ intersperse ", " vl') ++ "); // initVar\n")
          (_, Lf v) -> return (CodeV $ vid ++ " = " ++ tname ++ "(" ++ v ++ "); // initVar\n")
      -- if it is a null var, don't init it 
      Nothing -> return (CodeV $ "// initVar " ++ vid ++ " :: null.\n")
  other -> error $ "gen:initVar: can't init a struct var with an id tree. must be a leaf!\n" ++ (show var)
initVar val = gerr "initVar" val

{-g2 :: (Monad m, MonadCatch m) => Generator m
g2 [TyV ty] = (CodeV scode)
  where (sid, scode) = decStruct ty-}

-- DECARRAY(VAR, COUNTVAR)
-- -------------------------

decArr :: (Monad m, MonadCatch m) => Generator m
decArr [VarV ty var, VarV ity (Lf cntVar)] | ity == intTy || ity == uintTy = do
  -- get normal declarations
  (CodeV decs) <- decVar [VarV ty var]
  -- add square brackets with counts for each
  let postfix = "[" ++ cntVar ++ "];"
  let code = replace (pack ";") (pack postfix) (pack decs)
  return $ CodeV $ unpack code
decArr val = gerr "decArr" val

-- PRINT(VAR)
-- -------------

-- |printSt indent vid. Generates a print statement to display the variable.
printSt :: String -> Id -> Code
--printSt indent vid = "System.out.print(\"" ++ indent ++ "\");\n" ++
--  "System.out.println(" ++ vid ++ ");\n" 
printSt indent vid = "printVal(" ++ vid ++ ");\n";

printTup :: String -> [Code] -> Code
printTup indent printSts = printWithBrackets
  where printWithCommas = concat $ intersperse (printSt indent "\", \"") printSts
        printWithBrackets = (printSt indent "\"(\"") ++ printWithCommas ++ (printSt indent "\")\"") 

-- |printVar indent varId type. Generates print statements to display the variable.
printVar :: (Monad m, MonadCatch m) => String -> Id -> Ty -> GenM1 m Code
printVar indent vid ty = case ty of
  -- do leaf type
  Lf lty -> case lty of
    _ | isScalTy ty -> if ty == nullTy then return "" else return $ printSt indent vid
    ListTy et -> return "// print list"
    OMapTy kt vt -> do
      keyName <- genTypeName kt
      valName <- genTypeName vt
      case (keyName, valName) of
        (Just kn, vn) -> return $ "printVal<std::map<" ++ kn ++ ", " ++ (fromMaybe "nullStruct" vn) ++ "> >(" ++ vid ++ ");\n"
        other -> error $ "printVar:OMapTy: can't have an OMap with a null key type!"
    HMapTy kt vt -> do
      keyName <- genTypeName kt
      valName <- genTypeName vt
      case (keyName, valName) of
        (Just kn, vn) -> return $ "printVal<" ++ kn ++ ", " ++ (fromMaybe "nullStruct" vn) ++ ">(" ++ vid ++ ");\n"
        other -> error $ "printVar:HMapTy: can't have an HMap with a null key type!"
    other -> error $ "printVarGen: Can't print var of type " ++ (show ty)  
  -- work out struct names for the tuple
  Tup lty -> do 
    printMems <- mapM (\(ty,idx) -> printVar (indent ++ "  ") (vid ++ ".v" ++ (show idx)) ty) $ zip lty [treeIndexBase..]
    return $ printTup indent printMems
  -- else: error
  other -> error $ "Generators:printVar: Can't generate printVar code for " ++ vid ++ " of type " ++ (show other)

-- |printVars vars. Returns code to print the values of the vars.
printVars :: (Monad m, MonadCatch m) => String -> Tree (Id, Ty) -> GenM1 m Code
printVars indent vars = case vars of
  Lf (vid, ty) -> printVar indent vid ty
  Tup l        -> do
    sts <- mapM (\treeNode -> printVars (indent ++ "  ") treeNode) l
    return $ printTup indent $ sts
  other -> error $ "Generators:printVars: Can't display vars " ++ (show other)

-- |printVarGen [VarV type var]. Generates code to display var on the
-- |standard output.
printVarGen :: (Monad m, MonadCatch m) => Generator m
printVarGen arg@[VarV ty var] = do
  -- align type and id trees
  let tree = zipTrees ("printVarGen" ++ (show arg)) var ty
  -- print trees by case
  code <- printVars "" tree
  return $ CodeV code
printVarGen val = gerr "printVarGen" val

-- |genStructPrint structName type. Generates a printVal method for
-- |the struct.
genStructPrint :: (Monad m, MonadCatch m) => Id -> Ty -> GenM1 m Code
genStructPrint strName ty = do
  -- expand ids to access all scalars in tuple type
  let idTree = expandIdTree (Lf "v") ty
  -- generate recursive printing
  let idTyTree1 = zipTrees ("genStructPrint" ++ (show (strName, ty))) idTree ty
  code <- printVars "" idTyTree1
  -- generate method 
  let code1 = "void printVal(const " ++ strName ++ "& v) {\n" ++
             code ++ "\n" ++
             "}\n"
  -- return it
  return code1 

-- ASSIGN(DEST_VAR, SRC_VAR)
-- ---------------------------
-- Each ID in the ID trees are seperate vars, and individual
-- ids of tuple type are stored as structs.
-- Copies scalars by value, and other values by reference. 
-- Dest var must already have been declared.

-- |ifNull ty nullV notNullV. If ty is the Null type then
-- |returns nullV, else notNullV.
ifNull :: Ty -> v -> v -> v
ifNull ty nullV notNullV = case ty of
  Lf (NullTy) -> nullV
  _           -> notNullV

-- |singleAss (destVar, srcVar). Generates code that assigns srcVar to destVar.
singleAss :: (Monad m, MonadCatch m) => (Tree (Id, Ty), Tree (Id, Ty)) -> GenM1 m Code
singleAss destSrc = case destSrc of 
  -- simple id = id
  (Lf (destId, destTy), Lf (srcId, srcTy)) -> case destTy of
    -- don't assign a null type
    (Lf NullTy) -> return ""
    (Lf (LfTy "Null" [])) -> return ""
    -- copy sptr vecmaps by value, not by pointer
    _ | copyByVal destTy -> return $ "*" ++ destId ++ " = *" ++ srcId ++ "; // copy by val: " ++ (show destTy) ++ " = " ++ (show srcTy) ++ "\n"
    -- assign every other scalar
    other       -> return $ destId ++ " = " ++ srcId ++ "; //" ++ (show destTy) ++ " = " ++ (show srcTy) ++ "\n"
  -- id = tuple (recurse through tuple on rhs)
  (Lf (destId, Tup destTyLst), Tup srcLst) | length destTyLst == length srcLst -> do
    l <- mapM (\(idx,ty,src) -> 
      ifNull ty (return "") $ singleAss (Lf (destId ++ ".v" ++ (show idx), ty), src)) 
      $ zip3 [treeIndexBase..] destTyLst srcLst 
    return $ concat l
  -- tuple = id (recurse through tuple on lhs)
  (Tup destLst, Lf (srcId, Tup srcTyLst)) | length destLst == length srcTyLst -> do
    l <- mapM (\(idx,ty,dest) -> 
      ifNull ty (return "") $ singleAss (dest, Lf (srcId ++ ".v" ++ (show idx), ty))) 
      $ zip3 [treeIndexBase..] srcTyLst destLst 
    return $ concat l
  -- can't do any other assignment
  (otherDest, otherSrc) -> genError $ "singleAss: Can't generate assignment " ++ (show otherDest) ++ " = " ++ (show otherSrc)

-- |assignVarGen [destVar, srcVar]. Generates code that assigns srcVar to destVar.
assignVarGen :: (Monad m, MonadCatch m) => Generator m
assignVarGen arg@[VarV destTy destId, VarV srcTy srcId] = do
  -- check types match
  debug <- gets genDebugOut
  if destTy /= srcTy 
    then genError $ "assignVarGen: type mismatch: " ++ (show destTy) ++ " != " ++ (show srcTy)
    else return ()
  -- align types and id trees
  let errMsg = "assignVarGen" ++ (show arg)
  let typedDest = zipTrees (errMsg ++ "typedDest") destId destTy
  let typedSrc = zipTrees (errMsg ++ "typedSrc") srcId srcTy  
  let assList = zipSubTrees typedDest typedSrc
  -- code generate an assignment for each
  codes <- mapM singleAss assList
  let code = concat codes 
  return $ CodeV code

-- EQUALS(RESVAR, AVAR, BVAR)
-- ----------------

-- |eqGen [aVar, bVar]. Generates an expression to compare aVar and bVar.
eqGen :: (Monad m, MonadCatch m) => Generator m
eqGen arg@[VarV aTy aId, VarV bTy bId] | aTy == bTy = case aTy of
  -- compare scalars
  (Lf t) -> case (aId, bId) of
      (Lf a, Lf b) -> case t of
        _ | isScalTy aTy -> if aTy == nullTy 
          then return $ CodeV $ "1" -- null vals are always equal
          else return $ CodeV $ "(" ++ a ++ " == " ++ b ++ ")"
        ListTy elTy -> error "TODO: eqGEN:List"
        OMapTy kt vt -> return $ CodeV $ "(" ++ a ++ " == " ++ b ++ ")"
        HMapTy kt vt -> return $ CodeV $ "(" ++ a ++ " == " ++ b ++ ")"
        other -> genErrorC $ "gen:eqGen: can't compare vars of type " ++ (show t)
      other -> genErrorC $ "gen:eqGen: vars of scalar type, must just be a single leaf id, not: " 
                 ++ (show aId) ++ " or " ++ (show bId)
  -- compare tuples 
  (Tup l) -> do
      -- expand id trees to access struct members where neccesary
    let aid = expandIdTree aId aTy
    let bid = expandIdTree bId aTy
    -- make types dandgle from ids
    let aWithTypes = zipTrees ("eqGen" ++ (show arg)) aid aTy
    -- align them, and get list of ids to compare
    let pairs = alignTrees ("eqGen" ++ (show arg)) aWithTypes bid
    let cmpList = map (\((a, Lf t), Lf b) -> (Lf t, a, b)) pairs
    -- make first comparision
    let (fstTy, fstA, fstB) = head cmpList
    (CodeV cmpFirst) <- eqGen [VarV fstTy (Lf fstA), VarV fstTy (Lf fstB)]
    -- fold to make comparisons
    cmpCode <- foldlM (\prevCmp -> \(t, a, b) -> do
         (CodeV eqCmp) <- eqGen [VarV t (Lf a), VarV t (Lf b)];
         let cd = prevCmp ++ " && " ++ eqCmp
         return cd) cmpFirst (tail cmpList)
    return $ CodeV cmpCode
  -- can't compare objects of function type
  other  -> genErrorC $ "gen:eqGen: can't compare variables of type " ++ (show aTy)
eqGen val = gerr "eqGen" val

genStructEq :: (Monad m, MonadCatch m) => Id -> Ty -> GenM1 m Code
genStructEq structName ty = do
  let (Tup tyL) = ty
  let aId = Tup $ map (\idx -> Lf $ "v" ++ (show idx)) [treeIndexBase..((length tyL)-1)]
  (CodeV cmp) <- eqGen [VarV ty aId, VarV ty (Lf "b")]
  -- generate method 
  let code = "inline bool operator==(const " ++ structName ++ "& b) const {\n" ++
             "  return " ++ cmp ++ ";\n" ++
             "}\n" ++
             "inline bool operator!=(const " ++ structName ++ "& b) const {\n" ++
             "  return !(" ++ cmp ++ ");\n" ++
             "}\n"
  -- return it
  return code 

genEqStruct :: (Monad m, MonadCatch m) => Id -> Ty -> GenM1 m Code
genEqStruct structName ty = do
  let (Tup tyL) = ty
  let aId = Tup $ map (\idx -> Lf $ "v" ++ (show idx)) [treeIndexBase..((length tyL)-1)]
  (CodeV cmp) <- eqGen [VarV ty (Lf "a"), VarV ty (Lf "b")]
  -- generate struct
  let code = "struct eq" ++ structName ++ " {\n"++
             "inline bool operator()(const " ++ structName ++ "& a, const " ++ structName ++ "& b) const {\n" ++
             "  return " ++ cmp ++ ";\n" ++
             "}\n" ++
             "};\n"
  -- return it
  return code  

-- |genCollectionEqMethod className. Returns code for the == operator between
-- |the collections.
genCollectionEqMethod :: String -> Code
genCollectionEqMethod className = applyT eqCollectionTemplate [("T", className)]

-- |eqCollectionTemplate. Template for collection equality operator implementations.
-- |Collections are only equal, if they have the same values in the same order. 
eqCollectionTemplate :: StrTem
eqCollectionTemplate = "\
\ // compare <T> \n\
\ bool operator==(const <T> a, const <T> b) {\n\
\  if (a.size() != b.size()) return false;\n\
\  <T>::const_iterator itA, itB;\n\
\  for (itA = a.begin(), itB = b.ghc --mbegin();\n\
\       itA != a.end() && itB != b.end();\n\
\       ++itA, ++itB) \n\
\  {\n\
\    if ((*itA) != (*itB)) return false;\n\
\  }\n\
\  return true;\n\
\ }\n"

-- LESS THAN(AVAR, BVAR)
-- -------------------------

-- |ltGen [aVar, bVar]. Generates code to compare aVar and bVar.
ltGen :: (Monad m, MonadCatch m) => Generator m
ltGen arg@[VarV aTy aId, VarV bTy bId] | aTy == bTy = case aTy of
  -- scalars
  (Lf t) -> case (aId, bId) of
    (Lf avar, Lf bvar) -> case t of
      _ | isScalTy aTy -> if aTy == nullTy 
        then return $ CodeV "0" -- null vals are always equal so never less than
        else return $ CodeV $ "(" ++ avar ++ " < " ++ bvar ++ ")"
      other -> error $ "ltGen: not implemented, other scalar type comparisons"
    other -> error $ "ltGen: vars of scalar type must be id leaves!" 
  -- tuples     ifnVarInit "decDArr" outVarName (Lf "l") outT (Just $ Lf "mpiFloat")
  (Tup tl) -> do
    -- expand id trees to access struct members where neccesary
    let aid = expandIdTree aId aTy
    let bid = expandIdTree bId aTy
    -- make types dandgle from ids
    let aWithTypes = zipTrees ("ltGen" ++ (show arg) ++ "aWithTypes") aid aTy
    -- align them, and get list of ids to compare
    let pairs = alignTrees ("ltGen" ++ (show arg) ++ "pairs") aWithTypes bid
    let cmpList = map (\((a, Lf t), Lf b) -> (Lf t, a, b)) pairs
    -- make comparision for last element
    let (lastTy, lastA, lastB) = last cmpList
    (CodeV cmpLast) <- ltGen [VarV lastTy (Lf lastA), VarV lastTy (Lf lastB)]
    let cmpLast' = "(" ++ cmpLast  ++ ")"
    -- fold from right over rest to make comparisons
    let cmpListInit = init cmpList
    cmpCode <- foldrM (\(t, a, b) -> \innerCmp -> do 
        (CodeV ltCmp) <- ltGen [VarV t (Lf a), VarV t (Lf b)];
        (CodeV eqCmp) <- eqGen [VarV t (Lf a), VarV t (Lf b)];
        let cd = ltCmp ++ " || (" ++ eqCmp ++ " && (" ++ innerCmp ++ "))" 
        return cd) cmpLast' cmpListInit
    return $ CodeV cmpCode
  -- collections etc
  other -> error $ "ltGen: not implemented, can't compare vars of type " ++ (show aTy)
ltGen val = gerr "ltGen" val

-- |genStructMemLT structName memTypes. Returns a less than 
-- |comparision function for the struct.
genStructLT :: (Monad m, MonadCatch m) => Id -> Ty -> GenM1 m Code
genStructLT strName ty = do
  -- generate recursive comparison
  let (Tup tyL) = ty
  let aId = Tup $ map (\idx -> Lf $ "v" ++ (show idx)) [treeIndexBase..((length tyL)-1)] 
  (CodeV cmp) <- ltGen [VarV ty aId, VarV ty (Lf "b")]
  -- generate method 
  let code = "bool operator<(const " ++ strName ++ "& b) const {\n" ++
             "  return " ++ cmp ++ ";\n" ++
             "}\n" ++
             "bool operator>=(const " ++ strName ++ "& b) const {\n" ++
             "  return !(" ++ cmp ++ ");\n" ++
             "}\n"
  -- return it
  return code 

-- HASH(AVAR)
-- ---------------

-- |string template for flocc::hasher class implementations 
hashClassTemplate :: StrTem
hashClassTemplate = "\
 \ namespace flocc {\n\
 \   template<>\n\
 \   struct hasher<<structName>> {\n\
 \   public:\n\
 \       static inline hash_t hash(<structName> const& v) {\n\
 \           hash_t seed = 0;\n\
 \           <inner>\n\
 \           return seed;\n\
 \       }\n\
 \       inline hash_t operator()(const <structName>& v) const {\n\
 \         hash_t seed = 0;\n\
 \         <inner>\n\
 \         return seed;\n\
 \       }\n\
 \   };\n\
 \ }\n"

genHashFun :: (Monad m, MonadCatch m) => Id -> [(Int,Id)] -> GenM1 m Code
genHashFun structName members = case members of 
  -- empty type, no members
  [] -> do --error $ "Back:Generators:genHashFun: no members: " ++ (show structName) ++ "\n" ++ (show members)
    return $ applyT hashClassTemplate [("structName", structName), ("inner", "")]
  -- one member
  [(idx,tyName)] -> do
    let inner = "seed = hasher<" ++ tyName ++ ">::hash(v.v" ++ (show idx) ++ ");\n"
    return $ applyT hashClassTemplate [("structName", structName), ("inner", inner)] 
  -- two or more members
  members -> do
    let inner = concat $ map (\(idx,tname) -> "hash_combine<" ++ tname ++ ">(seed, v.v" ++ (show idx) ++ ");\n") members
    return $ applyT hashClassTemplate [("structName", structName), ("inner", inner)] 

-- USER REDUCTIONS

-- |redFunGen [funGraph]. Generates an MPI user defined reduction functions
-- |for distributed reductions.
redFunGen :: (Monad m, MonadCatch m) => Generator m
redFunGen [TyV elTy, GraphV {-inNid-} graph] = do
  genTrace "entered redFunGen"
  -- generate id for function
  funIdx <- newInt
  let funId = "userFun" ++ (show funIdx)
  -- create variables for body
  varExp (funId ++ "a") "bla" "in[i]" elTy
  varExp (funId ++ "b") "bla" "val2" elTy
  varExp (funId ++ "out") "bla" "out[i]" elTy
  aliasVar (Lf (funId ++"in")) (Tup [Lf (funId++"a"), Lf (funId++"b")])
  inVar <- getLocalVal (funId ++ "in")
  outVar <- getLocalVal (funId ++ "out")
  -- generate combineFun implementation
  combineCode <- evalFun (GraphV {-inNid-} graph) inVar emptyNodeTreeEx outVar
  -- get type name
  tyNameM <- genTypeName elTy
  let tyName = fromMaybe (error $ "redFunGen: couldn't gen type name for " ++ (show elTy)) tyNameM
  -- apply template
  let code = applyT redFunTemplate [("funId", funId), ("tyName", tyName), ("combineFun", combineCode)]
  -- output to declarations
  output "decls" code
  -- return function name
  genTrace "leaving redFunGen"
  return $ IdV funId

redFunTemplate :: StrTem
redFunTemplate = "\
\ // user def reduction function\n \
\ void <funId>(const void* invec, void *inoutvec, int len, const MPI::Datatype& datatype) {\n\
\   const <tyName>* in = (const <tyName>*)invec;\n\
\   <tyName>* out = (<tyName>*)inoutvec;\n\
\   // TODO: WHEN SENDING PROPER DATATYPE, CHANGE (len / sizeof(<tyName>)) to len!\n\
\   for (int i = 0; i < (len / sizeof(<tyName>)); i++) {\n\
\     <tyName> val2 = out[i];\n\
\     <combineFun>\n\
\  }\n\
\ }\n\n"

-- litArray(VAR, [Val])
-- -----------------------------

litArrayGen :: (Monad m, MonadCatch m) => Generator m
litArrayGen arg@[VarV (Lf (ListTy elemTy)) (Lf aId), ListV vals] = do
  tn <- genTypeName elemTy
  case tn of 
    Just tname -> do
      -- declare the array on the stack
      let code = tname ++ " " ++ aId ++ "[" ++ (show $ length vals) ++ "];\n"
      let code' = concat $ map (\(n,v) -> aId ++ "[" ++ (show n) ++ "] = " ++ (renderVal ("litArrayGen:arg=" ++ (show arg) ++ ":") ("lit array " ++ aId ++ "[" ++ (show n) ++ "]") v) ++ ";\n") $ zip [0..] vals
      -- init the array elements
      return $ CodeV $ code ++ code'
    Nothing    -> error $ "litArrayGen: could not generate type name for elements of type " ++ (show elemTy)

litArrayGenV :: (Monad m, MonadCatch m) => Generator m
litArrayGenV [IdV outVar, vals] = do
  -- lookup outVar from locals
  var <- getLocalVal outVar
  -- call using that var
  ret <- litArrayGen [var, vals]
  return ret

-- --------------------------------

-- |hashVar [inV, outV]. Returns code to assign, the hash of inV to outV.
hashVar :: (Monad m, MonadCatch m) => Generator m
hashVar arg@[inV@(VarV inTy inId), outV@(VarV (Lf (LfTy "Int" [])) (Lf outId))] = do
  -- if not a struct, copy to a struct
  r <- (case inId of
          -- call hash function, assigning to hash var
          (Lf v) -> return (v, "")
          -- assign to struct var, then hash
          (Tup l) -> do
            -- make new struct var
            num <- newInt
            let vid = "hashIn" ++ (show num)
            let inV' = VarV inTy (Lf vid)
            -- declare new struct var
            runGen "declareVar" ("dec" ++ vid) [inV']
            -- make assignment to struct var
            runGen "assignVar" ("copy" ++ vid) [inV', inV]
            -- get local context
            env <- getThisEnv
            -- expand the template using its values
            let code = applyTem ("hashVar:arg=" ++ (show arg) ++ ":") ("<dec" ++ vid ++ "><copy" ++ vid ++ ">\n") $ DM.toList env
            return (vid, code))
  let (inId', copyCode) = r
  -- then hash
  tyNameMb <- genTypeName inTy -- TODO if returns nothing, just assign the hash as 0 (e.g. for null type)
  case tyNameMb of
    -- null value
    Nothing -> return $ CodeV "outId = 0; // null type hash is 0\n"
    -- other
    Just tyName -> do
      --let tyName = fromMaybe (error $ "Back:Generators:hashVar: can't hash var of type " ++ (show inTy)) tyNameMb
      let hashCode = outId ++ " = flocc::hasher<" ++ tyName ++ ">::hash(" ++ inId' ++ ");\n"
      -- return code
      return $ CodeV $ copyCode ++ hashCode

-- arrayEl(ARRVAR, IDXVAR, STARTVAR)

generators :: (Monad m, MonadCatch m) => [(Id, Generator m)]
generators = [
  ("showType", g1),
  ("genTyName", genTyName),
  ("genMPITyName", genMPITyName),
  ("declareVar", decVar),
  ("declareVarInit", decInitVar),
  ("declareArr", decArr),
  ("initVar", initVar),
  ("printVar", printVarGen),
  ("assignVar", assignVarGen),
  ("eqVar", eqGen),
  ("ltVar", ltGen),
  ("reduceFun", redFunGen),
  ("hashVar", hashVar),
  ("litArr", litArrayGenV)--,
  --("arrayEl", arrayEl)
  ]



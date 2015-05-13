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
module Compiler.Back.Arrays where

import Compiler.Back.Graph (intTy, Tree(..))
import Compiler.Back.GenDecls
import Compiler.Back.Gen (createVar)

import Data.Maybe (fromMaybe)
import Data.List (intercalate, zip4)

-- |The type of array
-- |Jagged is accessed using IterDimZero
-- |Cont is accedded using IterOffset
data ArrTy = ArrJag | ArrCont
  deriving (Eq, Ord, Show)

-- |The type of array storage
data ArrStor = StorHeap | StorStack | StorStatic ConstArrSz
  deriving (Eq, Ord, Show)

-- |A constant array size
data ConstArrSz = ConstArrSz [Int]
  deriving (Eq, Ord, Show)

-- |Either an array lit of an integer var id
type ArrSzTy = String --ArrSzLit Int | ArrSzExp Code
  --deriving (Eq, Ord, Show)

arrSzLit :: Int -> ArrSzTy
arrSzLit n = show n

-- |Returns the expression code for an array size value
arrSzExp :: ArrSzTy -> Code
arrSzExp = id
{-arrSzExp sz = case sz of
  ArrSzLit v -> show v
  ArrSzExp e -> e-}

-- |Represents an index space to iterate over.
data IdxSpace = IdxSpace {
    idxStartExps :: [ArrSzTy],
    idxLimitExps :: [ArrSzTy],
    idxLenExps :: [ArrSzTy],
    idxStridExps :: [ArrSzTy] 
  } deriving (Eq, Show, Ord)

spaceNumDims :: IdxSpace -> Int
spaceNumDims (IdxSpace a b c d) = if n1 == n2 && n1 == n3 && n1 == n4 then n1 else error "Back/Arrays:spaceNumDims: invalid idxspace, differing num dims.\n"
  where n1 = length a
        n2 = length b
        n3 = length c 
        n4 = length c

-- |createSpaceFromLens starts lens strids. Creates a new Index space
-- |using lens, and works out limits based on them.
createSpaceFromLens :: [ArrSzTy] -> [ArrSzTy] -> [ArrSzTy] -> IdxSpace
createSpaceFromLens starts lens strids = IdxSpace starts lims lens strids
  where lims = map (\(st,len) -> "(" ++ st ++ " + " ++ len ++ ")") $ zipErr starts lens

-- |createSpaceFromLims starts lims strids. Creates a new Index space
-- |using lims, and works out lengths based on them.
createSpaceFromLims :: [ArrSzTy] -> [ArrSzTy] -> [ArrSzTy] -> IdxSpace
createSpaceFromLims starts lims strids = IdxSpace starts lims lens strids
  where lens = map (\(st,lim) -> "(" ++ lim ++ " - " ++ st ++ ")") $ zipErr starts lens

-- |Information about a particular array.
data ArrRec = ArrRec {
    arrTy :: ArrTy,
    arrStor :: ArrStor,
    arrElTy :: Id,
    arrNumDims :: Int,
    arrVarId :: Id, -- arr var
    arrSpace :: IdxSpace
  } deriving (Eq, Show, Ord)

-- |The type of array iterator
data ArrIterTy = IterOffset | IterStrided | IterDimsZero | IterDims
  deriving (Eq, Ord, Show) 

-- |Information about a particular array iterator.
data ArrIter = 
  ArrIterBase {
    arrIterTy :: ArrIterTy,
    arrIterExps :: [Code],
    arrIterIdxs :: IdxSpace 
  } | 
  ArrIterDerv {
    arrIterTy :: ArrIterTy,
    arrIterExps :: [Code]
  }
  deriving (Eq, Show, Ord)

zeros :: Int -> [ArrSzTy]
zeros n = take n $ repeat (arrSzLit 0)

ones :: Int -> [ArrSzTy]
ones n = take n $ repeat (arrSzLit 1)

{-

-- |Information about a particular array.
data ArrRec = ArrRec {
    arrTy :: ArrTy,
    arrStor :: ArrStor,
    arrNumDims :: Int,
    arrVarId :: Id, -- arr var
    arrLenVars :: [ArrSzTy], -- arr size vars
    arrStartVars :: [ArrSzTy]
  } deriving (Eq, Show, Ord)

-}

-- creates a new array var, and it's declaration.
createArr :: Monad m => ArrTy -> ArrStor -> IdxSpace -> Id 
  -> GenM1 m (ArrRec, Id, Code)
createArr arrTy stor space elTy = do
  -- create var for array
  arrNum <- newInt
  let arrVid = "arr" ++ (show arrNum) 
  -- create declaration for the array
  let lens = idxLenExps space
  let decDims = (case arrTy of
                   ArrJag  -> concat $ map (\l -> "["++(show l)++"]") lens
                   ArrCont -> "["++(foldl (\a -> \b -> a++"*"++b) "1" lens)++ "]")
  let decl = undefined
  -- create arr rec for the array
  -- init array to init values
  -- (TODO create a variable for reference counting/use a smart pointer???)
  -- TODO ....
  return undefined  

-- |isRangeValid start lim len strid. Returns code that throws an 
-- |error if this index range is invalid.
isRangeValid :: ArrSzTy -> ArrSzTy -> ArrSzTy -> ArrSzTy -> Code
isRangeValid start lim len strid = "if (" ++ preds ++ ")\n  " ++ throw
  where pred1 = "((" ++ lim ++ "-" ++ start ++ ")/" ++ strid ++ ") != " ++ len
        pred2 = "(" ++ lim ++ " >= " ++ start ++ ")" -- if start == lim the 0 elements
        pred3 = "(" ++ strid ++ " > 0)"  
        preds = pred1 ++ " && " ++ pred2 ++ " && " ++ pred3
        throw = "std::cerr << \"Invalid IdxSpace range.\"; throw 0;\n"

-- |zip4Err al bl cl dl. Zips together 4 lists, throwing an error if they differ in length.
zip4Err :: (Show a, Show b, Show c, Show d) => [a] -> [b] -> [c] -> [d] -> [(a,b,c,d)]
zip4Err al bl cl dl | length al == length bl && length al == length cl && length al == length dl = zip4 al bl cl dl
zip4Err al bl cl dl = error $ "Back/Arrays:zip4Err: list lengths differ: \n" ++ (show al) ++ "\n" ++ (show bl)

-- |isIdxSpaceValid space. Returns true if the lengths match the
-- |limits, and false otherwise.
isSpaceValid :: IdxSpace -> Code
isSpaceValid s = concat $ map (\(st,lm,ln,sr) -> isRangeValid st lm ln sr) l 
  where l = zip4Err (idxStartExps s) (idxLimitExps s) (idxLenExps s) (idxStridExps s)

type IdxRange = (ArrSzTy, ArrSzTy, ArrSzTy, ArrSzTy)

-- |isRangeSubset (ran1,ran2). Returns code that checks if ran2 is a subset of ran1,
-- |and throws an error if it isn't.
isRangeSubset :: (IdxRange, IdxRange) -> Code
isRangeSubset ((st1,lm1,ln1,sr1),(st2,lm2,ln2,sr2)) = "if (" ++ preds ++ ")\n  " ++ throw
  where pred1 = "((" ++ sr2 ++ "%" ++ sr1 ++ ") == 0)" -- subStride is multiple of stride
        pred2 = "(" ++ st2 ++ " >= " ++ st1 ++ " && " ++ st2 ++ " <= " ++ lm1 ++ ")"
        pred3 = "(" ++ lm2 ++ " >= " ++ st1 ++ " && " ++ lm2 ++ " <= " ++ lm1 ++ ")"
        pred4 = "(((" ++ st2 ++ "-" ++ st1 ++ ") % " ++ sr1 ++ ") == 0)"
        pred5 = "(((" ++ lm2 ++ "-" ++ st1 ++ ") % " ++ sr1 ++ ") == 0)"
        preds = pred1 ++ " && " ++ pred2 ++ " && " ++ pred3 ++ " && " ++ pred4 ++ " && " ++ pred5
        throw = "std::cerr << \"IdxSpace range is not a subset.\"; throw 0;\n"

-- |isSpaceSubset space subSpace. If subspace is not a subset of space
-- |then throws an error.
isSpaceSubset :: IdxSpace -> IdxSpace -> Code
isSpaceSubset s ss = concat $ map isRangeSubset $ zipErr l1 l2
  where l1 = zip4Err (idxStartExps s) (idxLimitExps s) (idxLenExps s) (idxStridExps s)
        l2 = zip4Err (idxStartExps ss) (idxLimitExps ss) (idxLenExps ss) (idxStridExps ss)

-- |spaceEqPredicate a b. Returns code to compare two IdxSpaces returning true 
-- |iff they are identical.
spaceEqPredicate :: IdxSpace -> IdxSpace -> Code
spaceEqPredicate a b = "(" ++ (intercalate " && " [p1,p2,p3,p4]) ++ ")"
  where p1 = intercalate " && " $ map (binOp "==") $ zip (idxStartExps a) (idxStartExps b) 
        p2 = intercalate " && " $ map (binOp "==") $ zip (idxLimitExps a) (idxLimitExps b) 
        p3 = intercalate " && " $ map (binOp "==") $ zip (idxLenExps a) (idxLenExps b) 
        p4 = intercalate " && " $ map (binOp "==") $ zip (idxStridExps a) (idxStridExps b) 

-- |declareIter iter. Returns code that declares the iterator
-- |variables, and assigns the iterator's start values to them.
declareIter :: ArrIter -> Code
declareIter it@(ArrIterBase _ _ _) = concat $ map (\(i,s) -> "int " ++ i ++ " = " ++ s ++ ";\n") vars
  where vars = zip (arrIterExps it) (idxStartExps $ arrIterIdxs it)
declareIter other = error $ "Back/Arrays:declareIter: can only declare base iterators: \n" ++ (show other)

-- |createArrIter arr itSpace. Returns a new iterator, to loop
-- |over the subarray, and the code to declare it.
createArrIter :: Monad m => ArrRec -> IdxSpace -> GenM1 m (Code, ArrIter)
createArrIter arr space = do
  -- check num dims are same in arr and space
  let ndims = arrNumDims arr
  if ndims == spaceNumDims space 
  then return () 
  else error $ "Back/Arrays:createArrIter: num dims in arr doesn't match space.\n"
  -- convert iter space to IterDimsZero
  let space0 = convertIdxSpace (arrSpace arr) IterDims IterDimsZero space 
  -- make new iter vars
  itVid <- newInt
  let vars = map (\i -> "it" ++ (show itVid) ++ "_" ++ (show i)) [0..(ndims-1)]
  -- make dims iterator (starts as dimsZero)
  let it1 = ArrIterBase { arrIterTy=IterDimsZero, arrIterExps=vars, arrIterIdxs=space0 }
  -- make iterator to access array
  case arrTy arr of
    -- a jagged array (all dims base 0)
    ArrJag -> do
      -- declare iter vars
      return (declareIter it1, it1)
    -- a contiguous array
    ArrCont -> do 
      -- make iterator strided
      let spaceS = convertIdxSpace (arrSpace arr) IterDimsZero IterStrided space0
      let it2 = ArrIterBase { arrIterTy=IterStrided, arrIterExps=vars, arrIterIdxs=spaceS }
      -- return (deriving an offset iterator)
      return (declareIter it2, deriveArrIter (arrSpace arr) IterOffset it2)

-- |accessElement arr iter. Returns an expression for accessing the
-- |element at the iterator's current position in the array.
accessElement :: ArrRec -> ArrIter -> Code
accessElement arr iter = case arrTy arr of
  -- jagged array
  ArrJag -> (arrVarId arr) ++ (concat $ map (\i -> "[" ++ i ++ "]") $ arrIterExps iter')
    where iter' = deriveArrIter (arrSpace arr) IterDimsZero iter
  -- contiguous array
  ArrCont -> case arrIterExps iter' of
      [offsetVid] -> (arrVarId arr) ++ "[" ++ offsetVid ++ "]"
      other -> error "Back/Arrays:accessElement: IterOffset iter should only have one exp.\n"
    where iter' = deriveArrIter (arrSpace arr) IterOffset iter

{-
-- |Represents an index space to iterate over.
data IdxSpace = IdxSpace {
    idxStartExps :: [ArrSzTy],
    idxLimitExps :: [ArrSzTy],
    idxLenExps :: [ArrSzTy],
    idxStridExps :: [ArrSzTy] 
  } deriving (Eq, Show, Ord)
-}

{-
-- |Information about a particular array iterator.
data ArrIter = 
  ArrIterBase {
    arrIterTy :: ArrIterTy,
    arrIterExps :: [Code],
    arrIterIdxs :: IdxSpace 
  } | 
  ArrIterDerv {
    arrIterTy :: ArrIterTy,
    arrIterExps :: [Code]
  }
  deriving (Eq, Show, Ord)

-}

-- |printLoopNests l. Prints l as a nested tree with the first pair
-- |starting and finishing the whole block, and the last pair at the middle.s
printLoopNests :: [(Code, Code)] -> Code
printLoopNests [] = ""
printLoopNests ((a,b):r) = a ++ (printLoopNests r) ++ b 

-- |createArrMpiType arr space elTyVid arrTyVid. Returns code to generate
-- |the MPI data type for a sub-array. Note: returned vars should be freed using delete []
-- |when the datatype is nolonger needed.
createArrMpiType :: Monad m => ArrRec -> IdxSpace -> Id -> Id -> GenM1 m (Code, [Id])
createArrMpiType arr space elTyVid arrTyVid = do
  -- check num dims are same in arr and space
  let ndims = arrNumDims arr
  if ndims == spaceNumDims space 
  then return () 
  else error $ "Back/Arrays:createArrMpiType: num dims in arr doesn't match space.\n"
  -- create vars
  vid <- newInt
  let blockIdxV = "blockIdx" ++ (show vid)
  let startPtrV = "startPtr" ++ (show vid) 
  let lensV = "arrLens" ++ (show vid) 
  let displsV = "arrDispls" ++ (show vid)
  let decVars = "int " ++ blockIdxV ++ " = 0;\n"++
                "void *" ++ startPtrV ++ ";\n"++
                "int *" ++ lensV ++ ";\nAint *" ++ displsV ++ ";\n" 
  -- generate contigious array case
  let pred1 = spaceEqPredicate (arrSpace arr) space
  let totalLen = foldl (\a -> \b -> a ++ "*" ++ b) "1" $ idxLenExps space
  let case1 = arrTyVid ++ " = " ++ elTyVid ++ ".Create_contiguous(" ++ totalLen ++ ");\n"
  -- generate last dim stride == arrStride case (cont chunks)
  let pred2 = (last $ idxStridExps space) ++ " == " ++ (last $ idxStridExps $ arrSpace arr)
  let numBlocks2 = foldl (\a -> \b -> a ++ "*" ++ b) "1" $ init $ idxLenExps space
  let blockLen2 = last $ idxLenExps space
  let newLims = (init $ idxLimitExps space) ++ ["(" ++ (last $ idxStartExps space) ++ "+1)"]
  let space2 = space { idxLimitExps=newLims, 
                       idxLenExps=(init $ idxLimitExps space) ++ ["1"],
                       idxStridExps=(init $ idxStridExps space) ++ ["1"] }
  (decIt2, it2) <- createArrIter arr space2
  let elPtr2 = "&(" ++ (accessElement arr it2) ++ ")"
  let loops2 = genLoops [it2] (defaultLoopDims ndims) 
  let inloop2 = lensV ++ "[" ++ blockIdxV ++ "] = " ++ blockLen2 ++ ";\n" ++
                displsV ++ "[" ++ blockIdxV ++ "] = " ++ elPtr2 ++ "-" ++ startPtrV ++ ";\n" ++
                blockIdxV ++ "++;\n"
  let case2 = decIt2 ++
              lensV ++ " = new int[" ++ numBlocks2 ++ "];\n" ++
              displsV ++ " = new Aint[" ++ numBlocks2 ++ "];\n"++
              startPtrV ++ " = " ++ elPtr2 ++ ";\n"++
              (printLoopNests $ loops2 ++ [(inloop2, "")])++
              arrTyVid ++ " = " ++ elTyVid ++ ".Create_hindexed(" ++ numBlocks2 ++ ", " 
                                              ++ lensV ++ ", " ++ displsV ++ ");\n"
  -- generate last dim stride /= arrStride case (single elements)
  let numBlocks3 = totalLen
  (decIt3, it3) <- createArrIter arr space
  let elPtr3 = "&(" ++ (accessElement arr it3) ++ ")"
  let loops3 = genLoops [it3] (defaultLoopDims ndims)
  let inloop3 = lensV ++ "[" ++ blockIdxV ++ "] = 1;\n" ++
                displsV ++ "[" ++ blockIdxV ++ "] = " ++ elPtr3 ++ "-" ++ startPtrV ++ ";\n" ++
                blockIdxV ++ "++;\n"  
  let case3 = decIt3 ++
              lensV ++ " = new int[" ++ numBlocks3 ++ "];\n" ++
              displsV ++ " = new Aint[" ++ numBlocks3 ++ "];\n"++
              startPtrV ++ " = " ++ elPtr3 ++ ";\n"++
              (printLoopNests $ loops3 ++ [(inloop3, "")])++
              arrTyVid ++ " = " ++ elTyVid ++ ".Create_hindexed(" ++ numBlocks3 ++ ", " 
                                               ++ lensV ++ ", " ++ displsV ++ ");\n"
  -- create branch for both cases
  let branch = decVars ++ 
               "if (" ++ pred1 ++ ") {\n" ++ case1 ++ -- whole array
               "} else {\nif (" ++ pred2 ++ ") {\n" ++ case2 ++ -- sub-array contiguous chunks
               "} else {\n" ++ case3 ++ "\n}}\n" -- sub-array single elements
  -- return code, and vars to free when possible
  return (branch, [lensV, displsV])

{-

    Nothing -> do
      -- create local var
      newVar localNames varTy
      -- create it's declaration
      case varVal of 
        Nothing   -> runGenV "declareVar" decName [localNames]
        Just valT -> runGenV "declareVarInit" decName [localNames, valT]
      -- assign to public member
      setVar (LLf (thisNid, []) ()) publicName localNames
      return ()

-}

-- TODO function to create a new iterator for an array
-- TODO another function for iterating over all elements in an array
--  (so if ArrCont iterates over all using a single index int)


decCInt :: Monad m => String -> Code -> GenM1 m (Code, Id)
decCInt c valExp = do
  -- new var
  (Lf varName) <- createVar intTy
  -- make declaration
  let decl = "const int " ++ varName ++ " = " ++ valExp ++ "; // " ++ c ++ "\n"
  return (varName, decl)

unpair :: [[(a,b)]] -> ([a], [[b]])
unpair lst = (as, bs)
  where pairs = map unzip lst
        as = concat $ map fst pairs
        bs = map snd pairs

-- |convertArrIter arr iter newIterTy. Takes one type of
-- |of iterator, and returns another iterator that iterates over
-- |the same space  
{-convertArrIter :: Monad m => 
  IdxSpace -> ArrIterTy -> ArrIter -> GenM1 m (Code, ArrIter)
convertArrIter idxSpace newIterTy iter =  do
  -- iter
  let ndims = length $ arrIterExps iter
  let oldIterTy = arrIterTy iter
  let iterSpace = arrIterIdxs iter
  let iterStarts = idxStartExps iterSpace
  let iterLimits = idxLimitExps iterSpace
  let spaceStarts = idxStartExps idxSpace
  let spaceLens = idxLenExps idxSpace
  -- switch on iter types
  case (oldIterTy, newIterTy) of
    -- if array iter type is not changing
    (old, new) | old == new -> return ("", iter)
    -- dims to dims0 (use zeros for starts, and subtract starts from limits)
    (IterDims, IterDimsZero) -> do
      sts <- mapM (\(i,s) -> decCInt "itSt" $ i ++ "-" ++ s) 
               $ zip iterStarts spaceStarts
      lms <- mapM (\(i,s) -> decCInt "itLim" $ i ++ "-" ++ s) 
               $ zip iterLimits spaceStarts
      let (decls, [newStarts, newLimits]) = unpair [sts, lms] 
      let iterIdxs' = iterSpace { idxStartExps=newStarts,
        idxLimitExps=newLimits }
      return (concat decls, iter { arrIterTy=newIterTy, arrIterIdxs=iterIdxs' } )
    (IterDimsZero, IterDims) -> do
      return undefined-}

binOp :: Code -> (Code, Code) -> Code
binOp op (a, b) = "(" ++ a ++ op ++ b ++ ")"

zipErr :: Show a => Show b => [a] -> [b] -> [(a,b)]
zipErr al bl | length al == length bl = zip al bl
zipErr al bl = error $ "Back/Arrays:zipErr: list lengths differ: \n" ++ (show al) ++ "\n" ++ (show bl)

-- |convertIdxSpace arrSpace iterSpace inTy outTy. Converts an iterater space iterSpace
-- |iterating over a subset of an array with space arrSpace, from inTy to outTy.
-- |Note: conversions to and from IterOffset are only allowed if iterSpace
-- |and arrSpace only have one dimension.
convertIdxSpace :: IdxSpace -> ArrIterTy -> ArrIterTy -> IdxSpace -> IdxSpace
convertIdxSpace arrSpace inTy outTy iterSpace = case (inTy, outTy) of
  -- already equal
  (inTy, outTy) | inTy == outTy -> iterSpace
  -- subtract arr starts from starts and limits
  (IterDims, IterDimsZero) -> iterSpace { idxStartExps=starts', idxLimitExps=limits' }
    where arrStarts = idxStartExps arrSpace
          starts' = map (binOp "-") $ zipErr (idxStartExps iterSpace) arrStarts
          limits' = map (binOp "-") $ zipErr (idxLimitExps iterSpace) arrStarts 
  (IterDimsZero, IterDims) -> iterSpace { idxStartExps=starts', idxLimitExps=limits' }
    where arrStarts = idxStartExps arrSpace
          starts' = map (binOp "+") $ zipErr (idxStartExps iterSpace) arrStarts
          limits' = map (binOp "+") $ zipErr (idxLimitExps iterSpace) arrStarts 
  -- multiply start, limit, and stride by product of less sig dim arr lengths
  (IterDimsZero, IterStrided) -> iterSpace { idxStartExps=starts', idxLimitExps=limits', idxStridExps=strids' }
    where strs = tail $ scanr (\a -> \b -> "("++a++"*"++b++")") "1" (idxLenExps arrSpace)
          starts' = map (binOp "*") $ zipErr strs $ idxStartExps iterSpace 
          limits' = map (binOp "*") $ zipErr strs $ idxLimitExps iterSpace
          strids' = map (binOp "*") $ zipErr strs $ idxStridExps iterSpace
  (IterStrided, IterDimsZero) -> iterSpace { idxStartExps=starts', idxLimitExps=limits', idxStridExps=strids' }
    where strs = tail $ scanr (\a -> \b -> "("++a++"*"++b++")") "1" (idxLenExps arrSpace)
          starts' = map (binOp "/") $ zipErr (idxStartExps iterSpace) strs 
          limits' = map (binOp "/") $ zipErr (idxLimitExps iterSpace) strs
          strids' = map (binOp "/") $ zipErr (idxStridExps iterSpace) strs
  -- only works for 1D spaces 
  (IterStrided, IterOffset) -> case idxStartExps iterSpace of
    l | length l == 1 -> iterSpace
    l -> error $ "Back/Arrays:convertIdxSpace: can't convert IdxSpace with >1 dim from strided to offset: " ++ (show iterSpace)
  (IterOffset, IterStrided) -> case idxStartExps iterSpace of
    l | length l == 1 -> iterSpace
    l -> error $ "Back/Arrays:convertIdxSpace: can't convert IdxSpace with >1 dim from offset to strided: " ++ (show iterSpace)
  -- indirect derivations, apply adjacent derv in correct direction
  other -> case other of
      (IterOffset, _) -> rec IterStrided outTy $ rec inTy IterStrided iterSpace
      (IterStrided, IterDims) -> rec IterDimsZero outTy $ rec inTy IterDimsZero iterSpace
      (IterDimsZero, IterOffset) -> rec IterStrided outTy $ rec inTy IterStrided iterSpace
      (IterDims, _) -> rec IterDimsZero outTy $ rec inTy IterDimsZero iterSpace
    where rec = convertIdxSpace arrSpace 

-- TODO create new arrIterExps????
-- or just the new IdxSpace??? 

  -- from dims to offset
  {-(IterDims, IterDimsZero) ->
  (IterDimsZero, IterOffset) ->
  -- from offset to dims
  (IterOffset, IterDimsZero) ->
  (IterDimsZero, IterDims) -> 
  -- missing out zero based dims
  (IterDims, IterOffset) ->
  (IterOffset, IterDims) -> -}

-- if the iter type is changing, then creates new index space based on
-- the original.

-- offset -> (need arr lens) -> dims zero -> (need arr starts) -> iter dims
-- iter dims -> (need arr starts) -> dims zero -> (need arr lens) -> offset
  
-- |deriveArrIter idxSpace targetIterType inputIter. Creates a new iterator
-- |from the original, by creating expressions for the new indices in terms
-- |of the input.
deriveArrIter :: IdxSpace -> ArrIterTy -> ArrIter -> ArrIter
deriveArrIter idxSpace outIterTy inIter = case (arrIterTy inIter, outIterTy) of
  -- if the same then just return
  (a, b) | a == b -> inIter
  -- subtract/add start indices of index space
  (IterDims, IterDimsZero) -> ArrIterDerv IterDimsZero exps 
    where exps = map (\(s,i) -> "(" ++ i ++ "-" ++ (arrSzExp s) ++ ")") 
                   $ zip (idxStartExps idxSpace) (arrIterExps inIter)
  (IterDimsZero, IterDims) -> ArrIterDerv IterDims exps
    where exps = map (\(s,i) ->  "(" ++ i ++ "+" ++ (arrSzExp s) ++ ")") 
                   $ zip (idxStartExps idxSpace) (arrIterExps inIter)
  -- multiply/divide each index by the index space width of that dim
  (IterDimsZero, IterStrided) -> ArrIterDerv IterStrided exps
    where strs = tail $ scanr (\a -> \b -> "("++a++"*"++b++")") "1" (idxLenExps idxSpace) 
          exps = map (\(s,i) -> i ++ "*" ++ s) $ zip strs (arrIterExps inIter)  
  (IterStrided, IterDimsZero) -> ArrIterDerv IterDimsZero exps
    where strs = tail $ scanr (\a -> \b -> "("++a++"*"++b++")") "1" (idxLenExps idxSpace) 
          exps = map (\(s,i) -> i ++ "/" ++ s) $ zip strs (arrIterExps inIter)
  -- sum strided indices
  (IterStrided, IterOffset) -> ArrIterDerv IterOffset [exp]
    where exp = intercalate "+" (map arrSzExp $ arrIterExps inIter)
  -- repeatedly modulo by strides (relies on common subexp elim for perf)
  (IterOffset, IterStrided) -> ArrIterDerv IterStrided exps 
    where off = head $ arrIterExps inIter
          strs = tail $ scanr (\a -> \b -> "("++a++"*"++b++")") "1" (idxLenExps idxSpace)
          mods = scanl (\a -> \b -> "(" ++ a ++ "%" ++ b ++ ")") off strs
          exps = map (\(s,m) -> "("++m++"/"++s++")") $ zip strs mods
  -- indirect derivations, apply adjacent derv in correct direction
  other -> case other of
      (IterOffset, _) -> fin $ rec IterStrided inIter
      (IterStrided, IterDims) -> fin $ rec IterDimsZero inIter
      (IterDimsZero, IterOffset) -> fin $ rec IterStrided inIter
      (IterDims, _) -> fin $ rec IterDimsZero inIter
    where rec = deriveArrIter idxSpace
          fin = rec outIterTy

-- decArrIter (dec and init at same time) :: ArrRec -> Code
-- (initArrIter :: )
-- convertArrIter :: ArrIterRec -> ArrIterRec -> Code
-- getArrIterDim :: ArrIterRec -> Int -> Id -> Code **
-- setArrIterDim :: ArrIterRec -> Int -> Id -> Code **
-- incArrIterDim :: ArrIterRec -> Int -> Code
-- incArrIter :: ArrIterRec -> Code

-- decAndInitArr :: ArrRec -> Code
-- (initArr)
-- freeArr :: ArrRec -> ()
-- getArrEl :: ArrIterRec -> IdTree -> Code **
-- setArrEl :: ArrIterRec -> IdTree -> Code
-- copyArr :: ArrRec -> ArrRec -> Code
-- getArrMPITy :: ArrRec -> [ArrSzTy] -> [ArrSzTy] -> Id -> Code
  
-- is it right to have each iterator connected to one array?
-- what about when for e.g. in eqjoin we want to have some
-- values shared between arrays, and to loop between the
-- max of the starts, and min of the ends.

-- |removeRepeats [] llist. Removes all repeats of
-- |an element found in an earlier sublist, from all
-- |the sublists that follow it.
removeRepeats :: Eq a => [a] -> [[a]] -> [[a]]
removeRepeats rem l = case l' of
    (h:r) -> h:(removeRepeats (rem++h) r)
    []    -> []
  where l' = map (filter (\a -> not $ elem a rem)) l

-- |defaultLoopDims numDims. Creates default loop dims for
-- |looping over a single array space with numDims dims.
defaultLoopDims :: Int -> [[(Int, Int)]]
defaultLoopDims ndims = map (\dim -> [(0, dim)]) [0..(ndims-1)]

-- |genLoops iters loopsDims. Generates a list of (nested) for loops, one for
-- |each element in loopsDims. Each element of loopDims defines a number of iterator dims
-- |(fst is iter idx, snd is iter's dim idx) that are to be iterated over in-step in a single 
-- |for-loop.
-- |Note: Can't loop over a derived iterator.
genLoops :: [ArrIter] -> [[(Int, Int)]] -> [(Code, Code)]
genLoops its loops = map (genLoop its) loops 

-- |dimAt idx lst. Gets the idx'th element of the list lst, returns an error if
-- |idx < 0 or gte the length of lst.
dimAt :: Show a => Int -> [a] -> a
dimAt dimIdx lst = if dimIdx >= 0 && dimIdx < length lst 
                   then lst !! dimIdx 
                   else error $ "Back/Arrays/genLoop: dim idx out of bounds: " ++ (show dimIdx) ++ "\n" ++ (show lst)

-- |genLoop iters loopDims. Generates a single for-loop that iterates over all the iterator dims
-- |listed in loopDims instep. Each element of loopDims is fst the iterator idx, and snd
-- |that iterator's dim idx.
genLoop :: [ArrIter] -> [(Int, Int)] -> (Code, Code)
genLoop its [] = ("", "") -- if no iterators, no loop
genLoop its dims = ("for (" ++ inits ++ "; " ++ preds ++ "; " ++ incs ++ ") {\n", "}\n")
  where dims' = map (\(itIdx,dimIdx) -> (if dimIdx >= 0 && dimIdx < length its 
                                         then its !! itIdx 
                                         else error $ "Back/Arrays/genLoop: iter idx out of bounds: " ++ (show itIdx),
                                         dimIdx)) dims
        iters = map (\(it,d) -> (dimAt d $ arrIterExps it, 
                                 dimAt d $ idxStartExps $ arrIterIdxs it,
                                 dimAt d $ idxLimitExps $ arrIterIdxs it,
                                 dimAt d $ idxStridExps $ arrIterIdxs it)) dims'
        inits = intercalate ", " $ map (\(it,st,_,_) -> it ++ " = " ++ st) iters
        preds = intercalate " && " $ map (\(it,_,en,_) -> it ++ " < " ++ en) iters
        incs  = intercalate ", " $ map (\(it,_,_,sr) -> it ++ " += " ++ sr) iters


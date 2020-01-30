{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module SAT.IPASIR.ComplexityProblemInstances where

import Data.Array
import Data.Ix (Ix(..))
import Data.Bifunctor (bimap)
import Foreign.C.Types (CInt)

import SAT.IPASIR.ComplexityProblem

data LBool = LFalse | LUndef | LTrue
    deriving (Show, Eq, Ord)

instance Enum LBool where
    toEnum = enumToLBool
    fromEnum LTrue  =  1
    fromEnum LUndef =  0
    fromEnum _      = -1

enumToLBool :: (Ord a, Num a) => a -> LBool
enumToLBool i = case compare i 0 of
    GT -> LTrue
    EQ -> LUndef
    _  -> LFalse

data FastSAT (m :: * -> *) e b = FastSAT

-- | The a representative of the 
--   [SAT-Problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem)
--   with variables of type e (will be an 'Enum' and 'Ix').
--   The 'Solution' is expressed using b (either 'Bool' or 'LBool').
type SAT e b = GeneralSAT e b [e] e

data GeneralSAT e b c a = GeneralSAT

-- | This reduction changes the 'Enum' representing the variables of the 
--   SAT-formula.
data SATRedEnum e i b = SATRedEnum

-- | This reduction changes the Boolean type from 'LBool' to 'Bool'.
--   Undefined Variables are set to 'False'.
data SATRedLBoolBool e = SATRedLBoolBool

instance (Enum e, Ix e, Monad m) => ComplexityProblem (FastSAT m e b) where
    type Encoding (FastSAT m e b) = [[e]]
    type Solution (FastSAT m e b) = e -> m b
    type Conflict (FastSAT m e b) = e -> m Bool
    type Assumption (FastSAT m e b) = e

instance (Enum e, Ix e) => ComplexityProblem (GeneralSAT e b c a) where
    type Encoding (GeneralSAT e b c a) = [[e]]
    type Solution (GeneralSAT e b c a) = Array e b
    type Conflict (GeneralSAT e b c a) = c
    type Assumption (GeneralSAT e b c a) = a

instance (Enum e, Ix e, Num e) => Solutiontransform (SAT e LBool) where
    solutionToEncoding    _ = map pure . sol2Enc ((*) . parseEnum)
    negSolutionToEncoding x = pure . map negate . sol2Enc ((*) . parseEnum)

instance (Enum e, Ix e, Num e) => Solutiontransform (SAT e Bool) where
    solutionToEncoding    _ = map pure . sol2Enc ((*) . pred . (*2) . parseEnum)
    negSolutionToEncoding x = pure . map negate . sol2Enc ((*) . pred . (*2) . parseEnum)

sol2Enc :: (Enum e, Ix e, Num e, Enum b) => (b -> e -> e) -> Array e b -> [e]
sol2Enc f = filter (/=0) . map (uncurry (flip f)) . assocs

instance (Enum e, Ix e) => Reduction (SATRedLBoolBool e) where
    type CPFrom (SATRedLBoolBool e) = SAT e LBool
    type CPTo   (SATRedLBoolBool e) = SAT e Bool
    newReduction = SATRedLBoolBool
    parseEncoding _ = (, SATRedLBoolBool)
    parseConflict _ = id
    parseSolution _ = fmap boolToLBool
    parseAssumption _ = pure

boolToLBool :: Bool -> LBool
boolToLBool True = LTrue
boolToLBool _    = LFalse

instance (Enum e, Enum i, Ix e, Ix i) => Reduction (SATRedEnum e i b) where
    type CPFrom (SATRedEnum e i b) = SAT e b
    type CPTo   (SATRedEnum e i b) = SAT i b
    newReduction = SATRedEnum
    parseEncoding _ encoding = ((map . map) parseEnum encoding, SATRedEnum)
    parseConflict _ = map parseEnum 
    parseSolution _ = mapIndex parseEnum
        where
            mapIndex :: (Ix e, Enum e, Ix i, Enum i) => (e -> i) -> Array i a -> Array e a
            mapIndex f arr = ixmap (bimap parseEnum parseEnum (bounds arr)) f arr
    parseAssumption _ = pure . parseEnum

parseEnum :: (Enum a, Enum b) => a -> b
parseEnum = toEnum . fromEnum

instance Ix CInt where
    range (from, to) = [from..to]
    index (from, to) i
      | inRange (from, to) i = fromEnum $ i - from
      | otherwise            = error $ "Index out of bounds Exception. Index:" 
                                        ++ show i ++ " Bounds: " ++ show (from,to)
    inRange (from, to) i = i >= from && i <= to
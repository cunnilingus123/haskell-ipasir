{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module SAT.IPASIR.SAT
    ( SAT (..)
    , SATRedLBoolBool (..)
    , SATRedBoolLBool (..)
    , SATRedEnum (..)
    , module Export
    ) where

import Data.Array (Array, assocs, bounds, ixmap)
import Data.Ix (Ix(..))
import Data.Bifunctor (bimap)
import Foreign.C.Types (CInt)

import SAT.IPASIR.ComplexityProblem as Export

-- | A representative of the 
--   [SAT-Problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem)
--   with variables of type e (will be an 'Enum').
--   The 'Solution' is expressed using b (either 'Bool' or 'LBool').
newtype SAT e b = SAT {satInstance :: [[e]]}

instance (Enum e, Ix e) => ComplexityProblem (SAT e b) where
    type Solution (SAT e b) = Array e b

instance (Enum e, Ix e) => AssumingProblem (SAT e b) where
    type Conflict   (SAT e b) = [e]
    type Assumption (SAT e b) = e

instance (Enum e, Ix e, Num e) => Solutiontransform (SAT e LBool) where
    solutionToEncoding    = SAT . map pure .              sol2Enc ((*) . parseEnum)
    negSolutionToEncoding = SAT .     pure . map negate . sol2Enc ((*) . parseEnum)

instance (Enum e, Ix e, Num e) => Solutiontransform (SAT e Bool) where
    solutionToEncoding    = SAT . map pure              . sol2Enc ((*) . pred . (*2) . parseEnum)
    negSolutionToEncoding = SAT .     pure . map negate . sol2Enc ((*) . pred . (*2) . parseEnum)

sol2Enc :: (Enum e, Ix e, Num e, Enum b) => (b -> e -> e) -> Array e b -> [e]
sol2Enc f = filter (/=0) . map (uncurry (flip f)) . assocs

-- | This reduction changes the Boolean type from 'Bool' to 'LBool'.
data SATRedLBoolBool e = SATRedLBoolBool

instance (Enum e, Ix e) => Reduction (SATRedLBoolBool e) where
    type CPFrom (SATRedLBoolBool e) = SAT e LBool
    type CPTo   (SATRedLBoolBool e) = SAT e Bool
    newReduction    = SATRedLBoolBool
    parseEncoding _ = (, SATRedLBoolBool) . SAT . satInstance
    parseSolution _ = fmap boolToLBool
        where
            boolToLBool :: Bool -> LBool
            boolToLBool True = LTrue
            boolToLBool _    = LFalse

instance (Enum e, Ix e) => AReduction (SATRedLBoolBool e) where
    parseConflict   _ = id
    parseAssumption _ = pure

-- | This reduction changes the Boolean type from 'LBool' to 'Bool'.
--   Undefined Variables are set to 'False'.
data SATRedBoolLBool e = SATRedBoolLBool

instance (Enum e, Ix e) => Reduction (SATRedBoolLBool e) where
    type CPFrom (SATRedBoolLBool e) = SAT e Bool
    type CPTo   (SATRedBoolLBool e) = SAT e LBool
    newReduction    = SATRedBoolLBool
    parseEncoding _ = (, SATRedBoolLBool) . SAT . satInstance
    parseSolution _ = fmap lboolToBool
        where
            lboolToBool :: LBool -> Bool
            lboolToBool LTrue = True
            lboolToBool _     = False

instance (Enum e, Ix e) => AReduction (SATRedBoolLBool e) where
    parseConflict   _ = id
    parseAssumption _ = pure

-- | This reduction changes the 'Enum' representing the variables of the 
--   SAT-formula.
data SATRedEnum e i b = SATRedEnum

instance (Enum e, Enum i, Ix e, Ix i) => Reduction (SATRedEnum e i b) where
    type CPFrom (SATRedEnum e i b) = SAT e b
    type CPTo   (SATRedEnum e i b) = SAT i b
    newReduction = SATRedEnum
    parseEncoding _ (SAT e) = (SAT $ (map . map) parseEnum e, SATRedEnum)
    parseSolution _ = mapIndex parseEnum
        where
            mapIndex :: (Ix e, Enum e, Ix i, Enum i) => (e -> i) -> Array i a -> Array e a
            mapIndex f arr = ixmap (bimap parseEnum parseEnum (bounds arr)) f arr

instance (Enum e, Enum i, Ix e, Ix i) => AReduction (SATRedEnum e i b) where
    parseConflict   _ = map parseEnum 
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

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module SAT.IPASIR.ComplexityProblems where

import SAT.IPASIR.Solver
import Data.Map (Map)
import Data.Bifunctor (bimap)
import Data.Array (Array, ixmap, bounds)
import Data.Ix (Ix(..))

data LBool = LFalse | LUndef | LTrue
    deriving (Show, Eq, Ord)

data SAT e b = SAT

data SATRedEnum e i b = SATRedEnum

instance (Enum e) => ComplexityProblem (SAT e b) where
    type Encoding (SAT e b) = [[e]]
    type Solution (SAT e b) = Array e b
    type Conflict (SAT e b) = [e]

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

parseEnum :: (Enum a, Enum b) => a -> b
parseEnum = toEnum . fromEnum

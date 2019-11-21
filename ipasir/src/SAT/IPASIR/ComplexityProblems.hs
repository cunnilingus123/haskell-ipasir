{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module SAT.IPASIR.ComplexityProblems where

import SAT.IPASIR.Solver
import Data.Map (Map)
import Data.Bifunctor (bimap)
import Data.Array (Array, ixmap, bounds)

-- | Some Solver give 
data LBool = LFalse | LUndef | LTrue
    deriving (Show, Eq, Ord)

data SAT e b = SAT

data SATRedEnum e i b = SATRedEnum

instance (Enum e) => ComplexityProblem (SAT e b) where
    type Encoding (SAT e b) = [[e]]
    type Solution (SAT e b) = Array e b
    type Conflict (SAT e b) = [e]

instance (Enum e, Enum i, Ord e) => Reduction (SATRedEnum e i b) where
    type CPFrom (SATRedEnum e i b) = SAT e b
    type CPTo   (SATRedEnum e i b) = SAT i b
    newReduction = SATRedEnum
    parseEncoding _ encoding = ((map . map) parseEnum encoding, SATRedEnum)
        where
         --   parseEnum :: e -> i
            parseEnum = toEnum . fromEnum
    parseResult _ = bimap (map parseEnum) undefined-- (mapIndex parseEnum)
        where
         --   parseEnum :: i -> e
            parseEnum = toEnum . fromEnum
            mapIndex f arr = ixmap (bounds arr) f arr
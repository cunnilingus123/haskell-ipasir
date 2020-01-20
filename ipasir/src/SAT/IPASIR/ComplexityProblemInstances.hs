{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module SAT.IPASIR.ComplexityProblemInstances where

import qualified Data.Map as M
import Data.Map (Map, fromList, mapKeys)
import Data.Array (Array, (!), ixmap, bounds)
import Data.Ix (Ix(..))
import Data.Bifunctor (bimap)
import Data.Functor.Identity (Identity(..))

import SAT.IPASIR.ComplexityProblem

data LBool = LFalse | LUndef | LTrue
    deriving (Show, Eq, Ord)

instance Enum LBool where
    toEnum = enumToLBool
    fromEnum LTrue  =  1
    fromEnum LUndef =  0
    fromEnum _      = -1

enumToLBool i = case compare i 0 of
    GT -> LTrue
    EQ -> LUndef
    _  -> LFalse

data FastSAT (m :: * -> *) e b = FastSAT

-- | The a representative of the 
--   [SAT-Problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem)
--   with variables of type e (will be an 'Enum' and 'Ix').
--   The 'Solution' is expressed using b (either 'Bool' or 'LBool').
data SAT e b = SAT

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

instance (Enum e, Ix e) => ComplexityProblem (SAT e b) where
    type Encoding (SAT e b) = [[e]]
    type Solution (SAT e b) = Array e b
    type Conflict (SAT e b) = [e]
    type Assumption (SAT e b) = e

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
    parseConflict _ = pure . map parseEnum 
    parseSolution _ = pure . mapIndex parseEnum
        where
            mapIndex :: (Ix e, Enum e, Ix i, Enum i) => (e -> i) -> Array i a -> Array e a
            mapIndex f arr = ixmap (bimap parseEnum parseEnum (bounds arr)) f arr
    parseAssumption _ = pure . parseEnum

parseEnum :: (Enum a, Enum b) => a -> b
parseEnum = toEnum . fromEnum

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module SAT.IPASIR.ComplexityProblem where

import Data.Map (Map)
import Data.Bifunctor (bimap)
import Data.Array (Array, ixmap, bounds)
import Data.Ix (Ix(..))
import Data.Proxy (Proxy(Proxy))

class ComplexityProblem cp where
    type Encoding cp
    type Solution cp
    type Conflict cp

-- | Every 'Solver' returns either a 'Solution' (also called model or proof)
--   for the complexity problem or a 'Conflict' if no solution exists.
type Result cp = Either (Conflict cp) (Solution cp)

-- | (👉) represents a new solver (or reduction) using a 'Reduction'.
--   The left side has to be an instance of 'Reduction' and the right 
--   side can either be a 'Solver', 'IncrementalSolver' or a 'Reduction'.
data reduction 👉 solver = reduction :👉 solver
infixr 3 👉
infixr 3 :👉

-- | A subclass of 'ComplexityProblem' which can make encodings
--   for a certain solution or makes an encoding, which refuses
--   a certain solution.
class (ComplexityProblem cp) => Solutiontransform cp where
    -- | Returns an encoding which will have a certain (unique) solution.
    solutionToEncoding    :: Proxy cp -> Solution cp -> Encoding cp
    -- | Returns an encoding for which every solution except the given 
    --   one is a valid.
    negSolutionToEncoding :: Proxy cp -> Solution cp -> Encoding cp

-- | A reduction parses one 'ComplexityProblem' into another.
class (ComplexityProblem (CPFrom r), ComplexityProblem (CPTo r)) => Reduction r where

    {-# MINIMAL newReduction, parseEncoding, 
        (parseSolution, parseConflict | parseResult) #-}

    type CPFrom r
    type CPTo   r
    -- | Sets up a new reduction layer. A reduction layer is only needed
    --   if you have to memorize stuff after a reduction. For example variable
    --   names. If you do not need, this one might a 'Data.Proxy.Proxy'
    newReduction  :: r
    -- | Parses an 'Encoding'. Notice, that the returned new reduction needs 
    --   to remember some renaming details like variablenames to parse a 
    --   'Solution' or a 'Conflict' back.  
    parseEncoding :: r -> Encoding (CPFrom r) -> (Encoding (CPTo r), r)
    -- | Parses a 'Solution' of a 'Solver' back.
    parseSolution :: r -> Solution (CPTo r) -> Solution (CPFrom r)
    parseSolution r s = case parseResult r $ Right s of Right s' -> s'
    -- | Parses a 'Conflict' of a 'Solver' back.
    parseConflict :: r -> Conflict (CPTo r) -> Conflict (CPFrom r)
    parseConflict r c = case parseResult r $ Left  c of Left  c' -> c'
    -- | Parses a 'Result' of a 'Solver' back.
    parseResult   :: r -> Result   (CPTo r) -> Result (CPFrom r)
    parseResult r = bimap (parseConflict r) (parseSolution r)

instance (Reduction r1, Reduction r2, CPFrom r2 ~ CPTo r1) => Reduction (r2 👉 r1) where
    type CPFrom (r2 👉 r1) = CPFrom r1
    type CPTo   (r2 👉 r1) = CPTo   r2
    newReduction  = newReduction :👉 newReduction
    parseEncoding (r2 :👉 r1) e = (e'', r'' :👉 r')
        where
            (e' ,r' ) = parseEncoding r1 e
            (e'',r'') = parseEncoding r2 e'
    parseSolution (r2 :👉 r1) = parseSolution r1 . parseSolution r2
    parseConflict (r2 :👉 r1) = parseConflict r1 . parseConflict r2

data LBool = LFalse | LUndef | LTrue
    deriving (Show, Eq, Ord)

data SAT e b = SAT

data SATRedEnum e i b = SATRedEnum

data SATRedLBoolBool e = SATRedLBoolBool

instance (Enum e) => ComplexityProblem (SAT e b) where
    type Encoding (SAT e b) = [[e]]
    type Solution (SAT e b) = Array e b
    type Conflict (SAT e b) = [e]

instance (Enum e) => Reduction (SATRedLBoolBool e) where
    type CPFrom (SATRedLBoolBool e) = SAT e LBool
    type CPTo   (SATRedLBoolBool e) = SAT e Bool
    newReduction = SATRedLBoolBool
    parseEncoding _ = (, SATRedLBoolBool)
    parseConflict _ = id
    parseSolution _ = fmap boolToLBool

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

parseEnum :: (Enum a, Enum b) => a -> b
parseEnum = toEnum . fromEnum

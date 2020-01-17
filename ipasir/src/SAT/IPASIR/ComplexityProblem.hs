{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module SAT.IPASIR.ComplexityProblem where

import Data.Map (Map, fromList, mapKeys)
import qualified Data.Map as M
import Data.Bifunctor (bimap)
import Data.Array (Array, (!), ixmap, bounds)
import Data.Ix (Ix(..))
import Data.Proxy (Proxy(Proxy))
import Control.Monad ((<=<))

class ComplexityProblem cp where
    type Encoding cp
    type Solution cp
    type Conflict cp
    type Assumption cp

-- | TODO: Die Namen sind noch doof.
--   Used for the type class 'SAT.IPASIR.Solver.PartSolver'.
--   Complexity classes which can split the 'Solution' into 
--   parts can offer more speed on generating the solution if
--   you do not want to know all the values.
--
--   This does not affect the speed of the solving process itself
--   but reduces the communication with the solver.
class (ComplexityProblem cp) => SolutionParts cp where
    type Part cp
    type SolutionPart cp
    shrinkSolution :: Proxy cp -> Part cp -> Solution cp -> SolutionPart cp

-- | Every 'Solver' returns either a 'Solution' (also called model or proof)
--   for the complexity problem or a 'Conflict' if no solution exists.
type Result cp = Either (Conflict cp) (Solution cp)

-- | TODO: Explain
type ResultSol cp solution = Either (Conflict cp) solution

-- | (👉) represents a new solver (or reduction) using a 'Reduction'.
--   If the left side 'r' is a 'Reduction' and the right side 's' is a 
-- 'SAT.IPASIR.Solver.Solver', an 'SAT.IPASIR.Solver.IncrementalSolver' or
-- 'Reduction', then 'r 👉 s' fullfills the same constraints like 's'.
data r 👉 s = r :👉 s
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
        (parseSolution, parseConflict | parseResult), parseAssumption #-}

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
    -- | Parses a 'Solution' of a 'ComplexityProblem' back.
    parseSolution :: r -> Solution (CPTo r) -> Solution (CPFrom r)
    parseSolution r s = case parseResult r (Right s) of Right s' -> s'
    -- | Parses a 'Conflict' of a 'ComplexityProblem' back.
    parseConflict :: r -> Conflict (CPTo r) -> Conflict (CPFrom r)
    parseConflict r c = case parseResult r (Left  c) of Left  c' -> c'
    -- | Parses a 'Result' of a 'ComplexityProblem' back.
    parseResult   :: r -> Result   (CPTo r) -> Result (CPFrom r)
    parseResult r = bimap (parseConflict r) (parseSolution r)
    -- | Parses the 'Assumption' into an equivalent sequence of other assumptions.
    parseAssumption :: r -> Assumption (CPFrom r) -> [Assumption (CPTo r)]

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
    parseAssumption (r2 :👉 r1) = parseAssumption r2 <=< parseAssumption r1

class (SolutionParts (CPFrom r), SolutionParts (CPTo r), Reduction r) => SPReduction r where
    parseSolutionPart :: forall f. Functor f =>
                         r -> (Part (CPTo   r) -> f (SolutionPart (CPTo   r))) 
                           -> (Part (CPFrom r) -> f (SolutionPart (CPFrom r)))

instance (SPReduction r1, SPReduction r2, CPFrom r2 ~ CPTo r1) => SPReduction (r2 👉 r1) where
    parseSolutionPart (r2 :👉 r1) = parseSolutionPart r1 . parseSolutionPart r2

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

instance (Enum e, Ix e) => ComplexityProblem (SAT e b) where
    type Encoding (SAT e b) = [[e]]
    type Solution (SAT e b) = Array e b
    type Conflict (SAT e b) = [e]
    type Assumption (SAT e b) = e

instance (Enum e, Ix e) => SolutionParts (SAT e b) where
    type Part (SAT e b) = e
    type SolutionPart (SAT e b) = b
    shrinkSolution _ part solution = solution ! part

instance (Enum e, Ix e) => Reduction (SATRedLBoolBool e) where
    type CPFrom (SATRedLBoolBool e) = SAT e LBool
    type CPTo   (SATRedLBoolBool e) = SAT e Bool
    newReduction = SATRedLBoolBool
    parseEncoding _ = (, SATRedLBoolBool)
    parseConflict _ = id
    parseSolution _ = fmap boolToLBool
    parseAssumption _ = pure

instance (Enum e, Ix e) => SPReduction (SATRedLBoolBool e) where
    parseSolutionPart _ f e = boolToLBool <$> f e

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

instance (Enum e, Enum i, Ix e, Ix i) => SPReduction (SATRedEnum e i b) where
    parseSolutionPart _ f = f . parseEnum 

parseEnum :: (Enum a, Enum b) => a -> b
parseEnum = toEnum . fromEnum

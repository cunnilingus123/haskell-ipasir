{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
-- {-# LANGUAGE LambdaCase #-}

module SAT.IPASIR.ComplexityProblem where

import Data.Proxy (Proxy(..))
import Data.Bifunctor (Bifunctor(..))
import Control.Monad ((<=<))

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

class ComplexityProblem cp where
    type Encoding cp
    type Solution cp

class (ComplexityProblem cp) => AssumingProblem cp where
    type Conflict cp
    type Assumption cp

-- | Every 'Solver' returns either a 'Solution' (also called model or proof)
--   for the complexity problem or a 'Conflict' if no solution exists.
type Result cp = Maybe (Solution cp)

-- | (👉) represents a new solver (or reduction) using a 'Reduction'.
--   If the left side 'r' is a 'Reduction' and the right side 's' is a 
-- 'SAT.IPASIR.Solver.Solver', an 'SAT.IPASIR.Solver.IncrementalSolver' or
-- 'Reduction', then 'r 👉 s' fullfills the same constraints like 's'.
data r 👉 s = r :👉 s
infixl 3 👉
infixl 3 :👉

instance Bifunctor (👉) where
    bimap f g (r :👉 s) = f r :👉 g s

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

    type CPFrom r
    type CPTo   r
    -- | Sets up a new reduction layer. A reduction layer is only needed
    --   if you have to memorize stuff after a reduction. For example variable
    --   names. In most cases this one will be 'Data.Proxy.Proxy'.
    newReduction  :: r
    -- | Parses an 'Encoding'. Notice, that the returned new reduction needs 
    --   to remember some renaming details like variablenames to parse a 
    --   'Solution' (or 'Conflict' or 'Assumption') back.
    parseEncoding :: r -> Encoding (CPFrom r) -> (Encoding (CPTo r), r)
    -- | Parses a 'Solution' of a 'ComplexityProblem' back.
    parseSolution :: r -> Solution (CPTo r) -> Solution (CPFrom r)

class (AssumingProblem (CPFrom r), AssumingProblem (CPTo r), Reduction r) 
      => AReduction r where
    -- | Parses a 'Conflict' of a 'ComplexityProblem' back.
    parseConflict :: r -> Conflict (CPTo r) -> Conflict (CPFrom r)
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
    parseSolution   (r2 :👉 r1) = parseSolution   r1  .  parseSolution   r2

instance (AReduction r1, AReduction r2, CPFrom r2 ~ CPTo r1) => AReduction (r2 👉 r1) where
    parseConflict   (r2 :👉 r1) = parseConflict   r1  .  parseConflict   r2
    parseAssumption (r2 :👉 r1) = parseAssumption r2 <=< parseAssumption r1

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module SAT.IPASIR.ComplexityProblem where

import Data.Proxy (Proxy(..))
import Data.Bifunctor (bimap)
import Control.Monad ((<=<))

class ComplexityProblem cp where
    type Encoding cp
    type Solution cp
    type Conflict cp
    type Assumption cp

-- | Every 'Solver' returns either a 'Solution' (also called model or proof)
--   for the complexity problem or a 'Conflict' if no solution exists.
type Result cp = Either (Conflict cp) (Solution cp)

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
    parseSolution r = (\case Right s' -> s'; _ -> undefined) . parseResult r . Right
    -- | Parses a 'Conflict' of a 'ComplexityProblem' back.
    parseConflict :: r -> Conflict (CPTo r) -> Conflict (CPFrom r)
    parseConflict r = (\case Left c'  -> c'; _ -> undefined) . parseResult r . Left
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
    parseSolution   (r2 :👉 r1) = parseSolution   r1  .  parseSolution   r2
    parseConflict   (r2 :👉 r1) = parseConflict   r1  .  parseConflict   r2
    parseAssumption (r2 :👉 r1) = parseAssumption r2 <=< parseAssumption r1

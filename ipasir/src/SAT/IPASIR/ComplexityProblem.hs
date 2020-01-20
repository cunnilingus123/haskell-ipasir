{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module SAT.IPASIR.ComplexityProblem where

import Data.Proxy (Proxy(Proxy))
import Data.Bifunctor (bimap)
import Data.Either (fromLeft, fromRight)
import Control.Monad ((<=<))
import Control.Arrow ((|||))

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
    parseSolution :: Monad m => r -> Solution (CPTo r) -> m (Solution (CPFrom r))
    parseSolution r s = fromRight (error err) <$> parseResult r (Right s)
    -- | Parses a 'Conflict' of a 'ComplexityProblem' back.
    parseConflict :: Monad m => r -> Conflict (CPTo r) -> m (Conflict (CPFrom r))
    parseConflict r c = fromLeft  (error err) <$> parseResult r (Left c)
    -- | Parses a 'Result' of a 'ComplexityProblem' back.
    parseResult   :: Monad m => r -> Result   (CPTo r) -> m (Result (CPFrom r))
    parseResult r = (fmap Left ||| fmap Right) . bimap (parseConflict r) (parseSolution r)
    -- | Parses the 'Assumption' into an equivalent sequence of other assumptions.
    parseAssumption :: r -> Assumption (CPFrom r) -> [Assumption (CPTo r)]

err = "Error on parsing a solution or conflict. This shouldn't happen :-("

instance (Reduction r1, Reduction r2, CPFrom r2 ~ CPTo r1) => Reduction (r2 👉 r1) where
    type CPFrom (r2 👉 r1) = CPFrom r1
    type CPTo   (r2 👉 r1) = CPTo   r2
    newReduction  = newReduction :👉 newReduction
    parseEncoding (r2 :👉 r1) e = (e'', r'' :👉 r')
        where
            (e' ,r' ) = parseEncoding r1 e
            (e'',r'') = parseEncoding r2 e'
    parseSolution   (r2 :👉 r1) = parseSolution   r1 <=< parseSolution   r2
    parseConflict   (r2 :👉 r1) = parseConflict   r1 <=< parseConflict   r2
    parseAssumption (r2 :👉 r1) = parseAssumption r2 <=< parseAssumption r1

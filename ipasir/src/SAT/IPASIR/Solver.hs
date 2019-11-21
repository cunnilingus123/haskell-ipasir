{-# LANGUAGE TypeFamilies
           , FunctionalDependencies
           , UndecidableInstances
           , ScopedTypeVariables
           , TypeOperators
           , FlexibleInstances
#-}

module SAT.IPASIR.Solver
    ( type(👉)((:👉))
    , Result
    , ComplexityProblem(..)
    , Solutiontransform(..)
    , Solver(..)
    , IncrementalSolver(..)
    , incrementalSolution
    , solveAll
    , Reduction(..)
    ) where

import Data.Either (isRight)
import Data.Proxy (Proxy(Proxy))
import Data.Bifunctor (bimap)

-- | Every 'Solver' returns either a 'Solution' (also called model or proof) for 
--   the complexity problem or a 'Conflict' if no solution exists.
type Result cp = Either (Conflict cp) (Solution cp)

-- | (👉) represents a new solver (or reduction) using a 'Reduction'. The left side 
-- has to be an instance of 'Reduction' and the right side can either be a 'Solver', 
-- 'IncrementalSolver' or a 'Reduction'.
data reduction 👉 solver = reduction :👉 solver
infixr 3 👉
infixr 3 :👉

class ComplexityProblem cp where
    type Encoding cp
    type Solution cp
    type Conflict cp

class (ComplexityProblem cp) => Solutiontransform cp where
    -- | Returns an encoding which will have a certain (unique) solution.
    solutionToEncoding    :: Proxy cp -> Solution cp -> Encoding cp
    -- | Returns an encoding for which every solution except the given one 
    --   is a valid.
    negSolutionToEncoding :: Proxy cp -> Solution cp -> Encoding cp

class (ComplexityProblem cp) => Solver solver cp | solver -> cp where
    -- | Calculates a model using the given solver. If the solver is a
    --  'IncrementalSolver', you can use the standard implementation 
    -- 
    -- > solution = incrementalSolution
    solution    :: Proxy solver -> Encoding cp -> Result cp
    -- | Same as checking if the result of 'solution' is a 'Solution'.
    satisfiable :: Proxy solver -> Encoding cp -> Bool
    satisfiable s e = isRight $ solution s e

class (Monad m, Solver solver cp) => IncrementalSolver m solver cp | solver -> m where
    -- | Creates a new empty 'IncrementalSolver'
    newIterativeSolver :: m solver
    -- | Adds contraints to the solver.
    addEncoding        :: solver -> Encoding cp -> m solver
    -- | starts the solving process and gives back the result. See 'Result'.
    solve              :: solver -> m (Result cp)
    -- | If the monad is "IO" you might want to implement this
    -- function by 'System.IO.Unsafe.unsafePerformIO' or 
    -- 'System.IO.Unsafe.unsafeDupablePerformIO'.
    unwrapMonadForNonIterative :: Proxy solver -> m a ->   a
    -- | Important for the lazyness on incremental solving. For example 'solveAll'
    -- does not compute lazy if this function is implemented by 'id'. If
    -- the monad is "IO", you might want to set this function
    -- to 'System.IO.Unsafe.unsafeInterleaveIO'.
    interleaveMonad           :: Proxy solver -> m a -> m a

incrementalSolution :: forall m solver cp. IncrementalSolver m solver cp => Proxy solver -> Encoding cp -> Result cp
incrementalSolution s encoding = unwrapMonadForNonIterative s $ do
    solver  <- newIterativeSolver :: m solver
    solver' <- addEncoding solver encoding
    solve solver'

-- | Like 'solution' but gives back every possible 'Solution'. For a lazy list,
-- you need to implement 'intercalateMonad' correctly. 
solveAll :: forall m solver cp. (IncrementalSolver m solver cp, Solutiontransform cp)
         => Proxy solver -> Encoding cp -> [Solution cp]
solveAll s encoding = unwrapMonadForNonIterative s $ do
    solver  <- newIterativeSolver :: m solver
    solver' <- addEncoding solver encoding
    looper solver'
  where
    looper :: solver -> m [Solution cp]
    looper solver = do
        res <- solve solver :: m (Result cp)
        case res of
            Left  _        -> pure []
            Right solution -> do
                solver' <- addEncoding solver 
                                $ negSolutionToEncoding (Proxy :: Proxy cp) solution
                sols <- interleaveMonad s $ looper solver'
                pure $ solution : sols

-- | A reduction parses one 'ComplexityProblem' into another.
class (ComplexityProblem cp1, ComplexityProblem cp2) 
      => Reduction reduction cp1 cp2 | reduction -> cp1, reduction -> cp2 where
    {-# MINIMAL newReduction, parseEncoding, (parseSolution, parseConflict | parseResult)  #-}
    -- | Sets up a new reduction layer. A reduction layer is only needed if you have to
    --   memorize stuff after a reduction. For example variable names. If you do not need,
    --   this one might a 'Data.Proxy.Proxy'
    newReduction  :: reduction
    -- | Parses an Encoding. Notice, that the returned new reduction needs to remember
    --   some renaming details like variablenames to parse a 'Solution' or a 'Conflict'
    --   back.  
    parseEncoding :: reduction -> Encoding cp1 -> (Encoding cp2, reduction)
    parseSolution :: reduction -> Solution cp2 -> Solution cp1
    parseSolution r s = case parseResult r $ Right s of Right s' -> s'
    parseConflict :: reduction -> Conflict cp2 -> Conflict cp1
    parseConflict r c = case parseResult r $ Left  c of Left  c' -> c'
    parseResult   :: reduction -> Result cp2   -> Result cp1
    parseResult r = bimap (parseConflict r) (parseSolution r)

instance (Reduction r1 cp1 cp2, Reduction r2 cp2 cp3)
         => Reduction (r2 👉 r1) cp1 cp3 where
    newReduction  = newReduction :👉 newReduction
    parseEncoding (r2 :👉 r1) e = (e'', r'' :👉 r')
        where
            (e' ,r' ) = parseEncoding r1 e
            (e'',r'') = parseEncoding r2 e'
    parseSolution (r2 :👉 r1) = parseSolution r1 . parseSolution r2
    parseConflict (r2 :👉 r1) = parseConflict r1 . parseConflict r2

instance (Reduction r cp1 cp2, Solver s cp2) => Solver (r 👉 s) cp1 where
    solution _ encoding = parseResult red $ solution (Proxy :: Proxy s) enc
        where
            (enc, red) = parseEncoding (newReduction :: r) encoding
    satisfiable _ encoding = satisfiable (Proxy :: Proxy s) enc
        where
            (enc, _) = parseEncoding (newReduction :: r) encoding

instance (Reduction r cp1 cp2, IncrementalSolver m s cp2) 
        => IncrementalSolver m (r 👉 s) cp1 where
    newIterativeSolver = (:👉) newReduction <$> newIterativeSolver
    addEncoding (r :👉 s) encoding = do
        let (encoding', r') = parseEncoding r encoding 
        s' <- addEncoding s encoding'
        return (r' :👉 s')
    solve (r :👉 s) = parseResult r <$> solve s
    unwrapMonadForNonIterative _ = unwrapMonadForNonIterative (Proxy :: Proxy s)
    interleaveMonad _            = interleaveMonad (Proxy :: Proxy s)

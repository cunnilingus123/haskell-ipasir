{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module SAT.IPASIR.Solver where

import Data.Either (isRight)
import Data.Proxy (Proxy(Proxy))
import Control.Monad (foldM)

import SAT.IPASIR.ComplexityProblem

class (ComplexityProblem (CPS s)) => Solver s where
    -- | The 'ComplexityProblem' this solver can solve.
    type CPS s
    -- | Calculates a model using the given solver. If the solver is an
    --  'IncrementalSolver', you can use the standard implementation:
    -- > solution = incrementalSolution
    solution    :: Proxy s -> Encoding (CPS s) -> Result (CPS s)
    -- | Same as checking if the result of 'solution' is a 'Solution'.
    satisfiable :: Proxy s -> Encoding (CPS s) -> Bool
    satisfiable s e = isRight $ solution s e

class (Monad (MonadIS s), Solver s) => IncrementalSolver s where
    -- | The Monad the @IncrementalSolver@ works in.
    type MonadIS s :: * -> *
    -- | Creates a new empty 'IncrementalSolver'
    newIterativeSolver :: MonadIS s s
    -- | Adds contraints to the solver.
    addEncoding        :: s -> Encoding (CPS s) -> MonadIS s s
    -- | Starts the solving process and gives back the result. See 'Result'.
    solve              :: s -> MonadIS s (Result (CPS s))
    assume             :: s -> Assumption (CPS s) -> MonadIS s s
    -- | If the monad is "IO" you might want to implement this
    --   function by 'System.IO.Unsafe.unsafePerformIO' or 
    --   'System.IO.Unsafe.unsafeDupablePerformIO'.
    unwrapMonadForNonIterative :: Proxy s -> MonadIS s a -> a
    -- | Important for the lazyness on incremental solving. 
    --   For example 'solveAll' does not compute lazy if this 
    --   function is implemented by 'id'. If the monad is "IO", 
    --   you might want to set this function to
    --   'System.IO.Unsafe.unsafeInterleaveIO'.
    interleaveMonad            :: Proxy s -> MonadIS s a -> MonadIS s a

-- | If you want to instantiate 'Solver' you can use this 
--   function as a standard implementation for 'solution'.
incrementalSolution :: forall s. IncrementalSolver s 
                    => Proxy s -> Encoding (CPS s) -> Result (CPS s)
incrementalSolution s encoding = unwrapMonadForNonIterative s $ do
    solver  <- newIterativeSolver :: MonadIS s s
    solver' <- addEncoding solver encoding
    solve solver'

-- | Like 'solution' but gives back every possible 'Solution'. For a lazy list,
--   you need to implement 'intercalateMonad' correctly. 
solveAll :: forall s. (IncrementalSolver s, Solutiontransform (CPS s))
         => Proxy s -> Encoding (CPS s) -> [Solution (CPS s)]
solveAll s encoding = unwrapMonadForNonIterative s $ do
    solver  <- newIterativeSolver :: MonadIS s s
    solver' <- addEncoding solver encoding
    looper solver'
  where
    looper :: s -> MonadIS s [Solution (CPS s)]
    looper solver = do
        res <- solve solver :: MonadIS s (Result (CPS s))
        case res of
            Left  _   -> pure []
            Right sol -> do
                solver' <- addEncoding solver 
                            $ negSolutionToEncoding (Proxy :: Proxy (CPS s)) sol
                sols <- interleaveMonad s $ looper solver'
                pure $ sol : sols

instance (Reduction r, Solver s, CPS s ~ CPTo r) => Solver (r 👉 s) where
    type CPS (r 👉 s) = CPFrom r
    solution _ encoding = parseResult red $ solution (Proxy :: Proxy s) enc
        where
            (enc, red) = parseEncoding (newReduction :: r) encoding
    satisfiable _ encoding = satisfiable (Proxy :: Proxy s) enc
        where
            (enc, _) = parseEncoding (newReduction :: r) encoding

instance (Reduction r, IncrementalSolver s, CPS s ~ CPTo r) 
          => IncrementalSolver (r 👉 s) where
    type MonadIS (r 👉 s) = MonadIS s
    newIterativeSolver = (:👉) newReduction <$> newIterativeSolver
    addEncoding (r :👉 s) encoding = do
        let (encoding', r') = parseEncoding r encoding 
        s' <- addEncoding s encoding'
        return (r' :👉 s')
    solve (r :👉 s) = parseResult r <$> solve s
    assume (r :👉 s) ass = fmap (r :👉) $ foldM assume s $ parseAssumption r ass
    unwrapMonadForNonIterative _ = unwrapMonadForNonIterative (Proxy :: Proxy s)
    interleaveMonad _            = interleaveMonad (Proxy :: Proxy s)

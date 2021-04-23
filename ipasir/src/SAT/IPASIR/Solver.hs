{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module SAT.IPASIR.Solver where

import Data.Bifunctor (bimap, first)
import Data.Proxy (Proxy(Proxy))
import Data.Maybe (isJust)
import Control.Monad (foldM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (runStateT, StateT(..), evalStateT, get, modify, put)

import SAT.IPASIR.ComplexityProblem
    ( AReduction(..)
    , Reduction(..)
    , Solutiontransform(negSolutionToEncoding)
    , type (👉)(..)
    , AssumingProblem(..)
    , ComplexityProblem(..)
    )

class (ComplexityProblem (CPS s)) => Solver s where
    -- | The 'ComplexityProblem' this solver can solve.
    type CPS s
    -- | Calculates a model using the given solver. If the solver is an
    --  'IncrementalSolver', you can use the standard implementation:
    -- > solution = incrementalSolution
    solution    :: Proxy s -> CPS s -> Maybe (Solution (CPS s))
    -- | Same as checking if the result of 'solution' is a 'Solution'.
    satisfiable :: Proxy s -> CPS s -> Bool
    satisfiable s e = isJust $ solution s e

type SolverMonad s a =  StateT s (MonadIS s) a

interleaveSolverMonad :: IncrementalSolver s => Proxy s
                                             -> SolverMonad s a
                                             -> SolverMonad s a
interleaveSolverMonad p sm = StateT $ interleaveMonad p . runStateT sm

class (Monad (MonadIS s), Solver s) => IncrementalSolver s where
    -- | The Monad the @IncrementalSolver@ works in.
    type MonadIS s :: * -> *
    -- | Creates a new empty 'IncrementalSolver'
    newIterativeSolver :: MonadIS s s
    -- | Adds contraints to the solver.
    addEncoding        :: CPS s -> SolverMonad s ()
    -- | Starts the solving process and gives back the result. See 'Result'.
    solve              :: SolverMonad s (Maybe (Solution (CPS s)))
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

class (IncrementalSolver s, AssumingProblem (CPS s)) => AssumingSolver s where
    assume        :: Assumption (CPS s) -> SolverMonad s ()
    solveConflict :: SolverMonad s (Either (Conflict (CPS s)) (Solution (CPS s)))

-- | If you want to instantiate 'Solver' you can use this 
--   function as a standard implementation for 'solution'.
incrementalSolution :: forall s. IncrementalSolver s 
                    => Proxy s -> CPS s -> Maybe (Solution (CPS s))
incrementalSolution s encoding 
    = unwrapSolverMonad s $ addEncoding encoding >> solve

runNewSolver :: IncrementalSolver s => Proxy s -> SolverMonad s a -> MonadIS s a
runNewSolver _ sm = evalStateT sm =<< newIterativeSolver

unwrapSolverMonad :: IncrementalSolver s => Proxy s -> SolverMonad s a -> a
unwrapSolverMonad s sm = unwrapMonadForNonIterative s $ runNewSolver s sm

-- | Like 'solution' but gives back every possible 'Solution'. For a lazy list,
--   you need to implement 'intercalateMonad' correctly. 
solveAll :: forall s. (IncrementalSolver s, Solutiontransform (CPS s))
         => Proxy s -> CPS s -> [Solution (CPS s)]
solveAll s encoding = unwrapSolverMonad s $ do
    addEncoding encoding
    looper
  where
    looper :: SolverMonad s [Solution (CPS s)]
    looper = do
        res <- solve
        case res of
            Nothing  -> pure []
            Just sol -> do
                addEncoding $ negSolutionToEncoding sol
                sols <- interleaveSolverMonad s looper 
                pure $ sol : sols

instance (Reduction r, Solver s, CPS s ~ CPTo r) => Solver (r 👉 s) where
    type CPS (r 👉 s) = CPFrom r
    solution _ encoding = parseSolution red <$> solution (Proxy :: Proxy s) enc
        where
            (enc, red) = parseEncoding (newReduction :: r) encoding
    satisfiable _ encoding = satisfiable (Proxy :: Proxy s) enc
        where
            (enc,   _) = parseEncoding (newReduction :: r) encoding

instance (Reduction r, IncrementalSolver s, CPS s ~ CPTo r) 
          => IncrementalSolver (r 👉 s) where
    type MonadIS (r 👉 s) = MonadIS s
    newIterativeSolver = (newReduction :👉) <$> newIterativeSolver
    addEncoding encoding = do
        r :👉 s <- get
        let (encoding', r') = parseEncoding r encoding
        modify $ first $ const r'
        liftReduction $ \_ -> addEncoding encoding'
    solve = liftReduction $ \r -> fmap (parseSolution r) <$> solve
    unwrapMonadForNonIterative _ = unwrapMonadForNonIterative (Proxy :: Proxy s)
    interleaveMonad _            = interleaveMonad (Proxy :: Proxy s)

instance (AReduction r, AssumingSolver s, CPS s ~ CPTo r) 
          => AssumingSolver (r 👉 s) where
    assume ass    = liftReduction $ \r -> mapM_ assume $ parseAssumption r ass
    solveConflict = liftReduction $ \r -> 
                      bimap (parseConflict r) (parseSolution r) <$> solveConflict

liftReduction :: IncrementalSolver s => (r -> SolverMonad s a) -> SolverMonad (r 👉 s) a
liftReduction f = do
    r :👉 s <- get
    (res,s') <- lift $ runStateT (f r) s
    put $ r :👉 s'
    return res

liftSolverMonad :: IncrementalSolver s => (s -> MonadIS s a) -> SolverMonad s a
liftSolverMonad f = lift . f =<< get

{-# LANGUAGE TypeFamilies
           , FunctionalDependencies
           , ScopedTypeVariables
           , TypeOperators
           , FlexibleInstances
           , FlexibleContexts
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

class (ComplexityProblem (CPS s)) => Solver s where
    type CPS s
    -- | Calculates a model using the given solver. If the solver is a
    --  'IncrementalSolver', you can use the standard implementation 
    -- 
    -- > solution = incrementalSolution
    solution    :: Proxy s -> Encoding (CPS s) -> Result (CPS s)
    -- | Same as checking if the result of 'solution' is a 'Solution'.
    satisfiable :: Proxy s -> Encoding (CPS s) -> Bool
    satisfiable s e = isRight $ solution s e

class (Monad (MonadIS s), Solver s) => IncrementalSolver s where
    type MonadIS s :: * -> *
    -- | Creates a new empty 'IncrementalSolver'
    newIterativeSolver :: MonadIS s s
    -- | Adds contraints to the solver.
    addEncoding        :: s -> Encoding (CPS s) -> MonadIS s s
    -- | starts the solving process and gives back the result. See 'Result'.
    solve              :: s -> MonadIS s (Result (CPS s))
    -- | If the monad is "IO" you might want to implement this
    -- function by 'System.IO.Unsafe.unsafePerformIO' or 
    -- 'System.IO.Unsafe.unsafeDupablePerformIO'.
    unwrapMonadForNonIterative :: Proxy s -> MonadIS s a -> a
    -- | Important for the lazyness on incremental solving. For example 'solveAll'
    -- does not compute lazy if this function is implemented by 'id'. If
    -- the monad is "IO", you might want to set this function
    -- to 'System.IO.Unsafe.unsafeInterleaveIO'.
    interleaveMonad            :: Proxy s -> MonadIS s a -> MonadIS s a

incrementalSolution :: forall s. IncrementalSolver s => Proxy s -> Encoding (CPS s) -> Result (CPS s)
incrementalSolution s encoding = unwrapMonadForNonIterative s $ do
    solver  <- newIterativeSolver :: MonadIS s s
    solver' <- addEncoding solver encoding
    solve solver'

-- | Like 'solution' but gives back every possible 'Solution'. For a lazy list,
-- you need to implement 'intercalateMonad' correctly. 
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
            Left  _        -> pure []
            Right solution -> do
                solver' <- addEncoding solver 
                                $ negSolutionToEncoding (Proxy :: Proxy (CPS s)) solution
                sols <- interleaveMonad s $ looper solver'
                pure $ solution : sols

-- | A reduction parses one 'ComplexityProblem' into another.
class (ComplexityProblem (CPFrom r), ComplexityProblem (CPTo r)) 
      => Reduction r where
    {-# MINIMAL newReduction, parseEncoding, (parseSolution, parseConflict | parseResult)  #-}
    type CPFrom r
    type CPTo   r
    -- | Sets up a new reduction layer. A reduction layer is only needed if you have to
    --   memorize stuff after a reduction. For example variable names. If you do not need,
    --   this one might a 'Data.Proxy.Proxy'
    newReduction  :: r
    -- | Parses an Encoding. Notice, that the returned new reduction needs to remember
    --   some renaming details like variablenames to parse a 'Solution' or a 'Conflict'
    --   back.  
    parseEncoding :: r -> Encoding (CPFrom r) -> (Encoding (CPTo r), r)
    parseSolution :: r -> Solution (CPTo r) -> Solution (CPFrom r)
    parseSolution r s = case parseResult r $ Right s of Right s' -> s'
    parseConflict :: r -> Conflict (CPTo r) -> Conflict (CPFrom r)
    parseConflict r c = case parseResult r $ Left  c of Left  c' -> c'
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
    unwrapMonadForNonIterative _ = unwrapMonadForNonIterative (Proxy :: Proxy s)
    interleaveMonad _            = interleaveMonad (Proxy :: Proxy s)

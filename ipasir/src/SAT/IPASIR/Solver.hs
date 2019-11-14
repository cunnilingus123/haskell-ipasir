{-# LANGUAGE TypeFamilies
           , MultiParamTypeClasses
           , FunctionalDependencies
           , UndecidableInstances
           , ScopedTypeVariables
           , FlexibleContexts
           , TypeOperators
#-}

module SAT.IPASIR.Solver where

import Data.Either (isRight)
import Data.Proxy (Proxy)
import Data.Bifunctor (second)

(💩) = (.) . (.)

type  Result solver = Either ( Conflict solver) ( Solution solver)
type IResult solver = Either (IConflict solver) (ISolution solver)

class Solver solver where
    type Encoding solver
    type Solution solver
    type Conflict solver

    solution    :: solver -> Encoding solver -> Result solver
    satisfiable :: solver -> Encoding solver -> Bool
    satisfiable = isRight 💩 solution

class Monad m => IterativeSolver solver m | solver -> m where
    type IEncoding solver
    type ISolution solver
    type IConflict solver

    newIterativeSolver :: m solver
    addEncoding        :: solver -> IEncoding solver -> m solver
    solve              :: solver -> m (IResult solver)

    unwrapmonadForNonIterative :: Proxy solver -> m a ->   a
    intercalateMonad           :: Proxy solver -> m a -> m a

class (Solver solver) => Solutiontransform solver where
    solutionToEncoding    :: Proxy solver -> Solution solver -> Encoding solver
    negSolutionToEncoding :: Proxy solver -> Solution solver -> Encoding solver

instance (IterativeSolver solver m) => Solver (Proxy solver) where
    type Encoding (Proxy solver) = IEncoding solver
    type Solution (Proxy solver) = ISolution solver
    type Conflict (Proxy solver) = IConflict solver

    solution s encoding = unwrapmonadForNonIterative s $ do
        solver <- newIterativeSolver :: m solver
        addEncoding solver encoding
        solve solver

solveAll :: forall solver m. (IterativeSolver solver m, Solutiontransform (Proxy solver))
         => Proxy solver -> IEncoding solver -> (IConflict solver, [ISolution solver])
solveAll s encoding = unwrapmonadForNonIterative s $ do
    solver <- newIterativeSolver :: m solver
    addEncoding solver encoding
    looper solver
  where
    looper :: solver -> m (IConflict solver, [ISolution solver])
    looper solver = do
        res <- solve solver :: m (IResult solver)
        case res of
            Left  conflict -> pure (conflict, [])
            Right solution -> do
                (c, sols) <- intercalateMonad s $ looper solver
                pure (c , solution : sols)
    
data reduction 👈 solver = reduction :👈 solver

{-
class (Solver s1, Solver s2) => Reduction s1 s2 r where
    reduceSolver :: r -> s1 -> s2

class (IterativeSolver s1 m, IterativeSolver s2 m) => IReduction s1 s2 m r where
    reduceISolver :: r -> s1 -> s2
-}
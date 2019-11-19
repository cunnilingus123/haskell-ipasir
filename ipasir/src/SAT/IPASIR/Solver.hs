{-# LANGUAGE TypeFamilies
           , FunctionalDependencies
           , UndecidableInstances
           , ScopedTypeVariables
           , TypeOperators
           , FlexibleInstances
#-}

module SAT.IPASIR.Solver where

import Data.Either (isRight)
import Data.Proxy (Proxy(Proxy))
import Data.Bifunctor (second,bimap)

(💩) = (.) . (.)

type Result solver = Either (Conflict solver) (Solution solver)

data reduction 👈 solver = reduction :👈 solver
infixr 3 👈
infixr 3 :👈

{-
solution s encoding = unwrapmonadForNonIterative s $ do
    solver  <- newIterativeSolver :: m solver
    solver' <- addEncoding solver encoding
    solve solver'
-}

class Solver solver where
    type Encoding solver
    type Solution solver
    type Conflict solver
    solution    :: Proxy solver -> Encoding solver -> Result solver
    satisfiable :: Proxy solver -> Encoding solver -> Bool
    satisfiable = isRight 💩 solution

class (Monad m, Solver solver) => IterativeSolver solver m | solver -> m where
    newIterativeSolver :: m solver
    addEncoding        :: solver -> Encoding solver -> m solver
    solve              :: solver -> m (Result solver)
    unwrapmonadForNonIterative :: Proxy solver -> m a ->   a
    intercalateMonad           :: Proxy solver -> m a -> m a

class (Solver solver) => Solutiontransform solver where
    solutionToEncoding    :: Proxy solver -> Solution solver -> Encoding solver
    negSolutionToEncoding :: Proxy solver -> Solution solver -> Encoding solver

solveAll :: forall solver m. (IterativeSolver solver m, Solutiontransform solver)
         => Proxy solver -> Encoding solver -> [Solution solver]
solveAll s encoding = unwrapmonadForNonIterative s $ do
    solver  <- newIterativeSolver :: m solver
    solver' <- addEncoding solver encoding
    looper solver'
  where
    looper :: solver -> m [Solution solver]
    looper solver = do
        (res :: Result solver) <- solve solver
        case res of
            Left  _        -> pure []
            Right solution -> do
                solver' <- addEncoding solver $ negSolutionToEncoding (Proxy :: Proxy solver) solution
                sols <- intercalateMonad s $ looper solver'
                pure $ solution : sols

instance (Reduction r s) => Solver (r 👈 s) where
    type Encoding (r 👈 s) = REncoding r
    type Solution (r 👈 s) = RSolution r
    type Conflict (r 👈 s) = RConflict r
    solution _ encoding = liftResult red $ solution (Proxy :: Proxy s) enc
      where
        (enc, red) = transEncoding (newReduction :: r) encoding
    satisfiable _ encoding = satisfiable (Proxy :: Proxy s) enc
      where
        (enc, _) = transEncoding (newReduction :: r) encoding

instance (IterativeSolver s m, Reduction r s) => IterativeSolver (r 👈 s) m where
    newIterativeSolver = (:👈) newReduction <$> newIterativeSolver
    addEncoding (r :👈 s) encoding = do
        let (encoding', r')= transEncoding r encoding 
        s' <- addEncoding s encoding'
        return (r' :👈 s')
    solve (r :👈 s) = liftResult r <$> solve s
    unwrapmonadForNonIterative _ = unwrapmonadForNonIterative (Proxy :: Proxy s)
    intercalateMonad _           = intercalateMonad (Proxy :: Proxy s)

liftResult :: Reduction reduction solver => reduction -> Result solver -> Result (reduction 👈 solver)
liftResult reduction = bimap (transConflict reduction) (transSolution reduction) 

class (Solver solver) => Reduction reduction solver | reduction -> solver where
    type REncoding reduction
    type RSolution reduction
    type RConflict reduction

    newReduction  :: reduction
    transEncoding :: reduction -> REncoding reduction -> (Encoding solver, reduction)
    transSolution :: reduction -> Solution solver -> RSolution reduction
    transConflict :: reduction -> Conflict solver -> RConflict reduction


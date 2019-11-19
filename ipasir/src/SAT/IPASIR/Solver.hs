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

class ComplexityProblem cp where
    type Encoding cp
    type Solution cp
    type Conflict cp

class (ComplexityProblem cp) => Solutiontransform cp where
    solutionToEncoding    :: Proxy cp -> Solution cp -> Encoding cp
    negSolutionToEncoding :: Proxy cp -> Solution cp -> Encoding cp

class (ComplexityProblem cp) => Solver solver cp | solver -> cp where
    solution    :: Proxy solver -> Encoding cp -> Result cp
    satisfiable :: Proxy solver -> Encoding cp -> Bool
    satisfiable s e = isRight $ solution s e

class (Monad m, Solver solver cp) => IterativeSolver m solver cp | solver -> m where
    newIterativeSolver :: m solver
    addEncoding        :: solver -> Encoding cp -> m solver
    solve              :: solver -> m (Result cp)
    unwrapmonadForNonIterative :: Proxy solver -> m a ->   a
    intercalateMonad           :: Proxy solver -> m a -> m a

solveAll :: forall m solver cp. (IterativeSolver m solver cp, Solutiontransform cp)
         => Proxy solver -> Encoding cp -> [Solution cp]
solveAll s encoding = unwrapmonadForNonIterative s $ do
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
                solver' <- addEncoding solver $ negSolutionToEncoding (Proxy :: Proxy cp) solution
                sols <- intercalateMonad s $ looper solver'
                pure $ solution : sols

class (ComplexityProblem cp1, ComplexityProblem cp2) 
      => Reduction reduction cp1 cp2 | reduction -> cp1, reduction -> cp2 where
    newReduction  :: reduction
    transEncoding :: reduction -> Encoding cp1 -> (Encoding cp2, reduction)
    transSolution :: reduction -> Solution cp2 -> Solution cp1
    transConflict :: reduction -> Conflict cp2 -> Conflict cp1

instance (Reduction r1 cp1 cp2, Reduction r2 cp2 cp3)
         => Reduction (r2 👈 r1) cp1 cp3 where
    newReduction  = newReduction :👈 newReduction
    transEncoding (r2 :👈 r1) e = (e'', r'' :👈 r')
        where
            (e' ,r' ) = transEncoding r1 e
            (e'',r'') = transEncoding r2 e'
    transSolution (r2 :👈 r1) = transSolution r1 . transSolution r2
    transConflict (r2 :👈 r1) = transConflict r1 . transConflict r2

instance (Reduction r cp1 cp2, Solver s cp2) => Solver (r 👈 s) cp1 where
    solution _ encoding = liftResult red $ solution (Proxy :: Proxy s) enc
      where
        (enc, red) = transEncoding (newReduction :: r) encoding
    satisfiable _ encoding = satisfiable (Proxy :: Proxy s) enc
      where
        (enc, _) = transEncoding (newReduction :: r) encoding

instance (Reduction r cp1 cp2, IterativeSolver m s cp2) => IterativeSolver m (r 👈 s) cp1 where
    newIterativeSolver = (:👈) newReduction <$> newIterativeSolver
    addEncoding (r :👈 s) encoding = do
        let (encoding', r')= transEncoding r encoding 
        s' <- addEncoding s encoding'
        return (r' :👈 s')
    solve (r :👈 s) = liftResult r <$> solve s
    unwrapmonadForNonIterative _ = unwrapmonadForNonIterative (Proxy :: Proxy s)
    intercalateMonad _           = intercalateMonad (Proxy :: Proxy s)

liftResult :: Reduction reduction cp1 cp2 => reduction -> Result cp2 -> Result cp1
liftResult reduction = bimap (transConflict reduction) (transSolution reduction) 

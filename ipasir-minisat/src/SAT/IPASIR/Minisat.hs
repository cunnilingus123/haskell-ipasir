{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module SAT.IPASIR.Minisat where

-- | A low-level Haskell wrapper around the MiniSat-All library.

import Foreign
import Foreign.C.Types
import Control.Monad (when, liftM2, liftM3)
import Control.Monad.Loops 
import Data.Proxy
import Foreign.ForeignPtr.Unsafe (unsafeForeignPtrToPtr)
import Data.IORef

import SAT.IPASIR.IpasirApi
import SAT.IPASIR.ComplexityProblemInstances (LBool(..), SAT(..))
import SAT.IPASIR.ComplexityProblem



-- Some Testing
import SAT.IPASIR.Solver
import Debug.Trace

g1 = do
  s1 <- newIterativeSolver :: IO Minisat
  s2 <- addEncoding s1 [[1,2,3,4],[-2,-3],[-1,-5]]
  assume s2 (-3)
  s3 <- addEncoding s2 [[-1,-5]]
  assume s3 4
  assume s3 5
  solve s3

-- ----------------------------------------------------------------------
-- * Some types

-- | An abstract type for the solver.
data CSolver = CSolver
data HSolver = HSolver (ForeignPtr CSolver) (IORef [CInt]) (Ptr CChar)
type Minisat = IpasirSolver HSolver
minisat :: Proxy Minisat
minisat = Proxy

-- ----------------------------------------------------------------------
-- * Conversions
toLit :: CInt -> CInt
toLit l = pos + pos + si
  where
    pos = abs l - 1
    si  = if l < 0 then 1 else 0
-- ----------------------------------------------------------------------
-- * C API functions

-- | Low-level wrapper around the C function /solver_new/.
foreign import ccall unsafe "solver.h solver_new"
  cNewSolver :: IO (Ptr CSolver)

-- | Low-level wrapper around the C function /solver_delete/.
foreign import ccall unsafe "solver.h solver_delete"
  cDelSolver :: Ptr CSolver -> IO ()

-- | Free a solver, callable by the garbage collector.
foreign import ccall unsafe "solver.h &solver_delete"
  cDelSolverGC :: FinalizerPtr CSolver

-- | Low-level wrapper around the C function /solver_addclause/.
foreign import ccall unsafe "solver.h solver_addclause"
  cSolverAddClause :: Ptr CSolver -> Ptr CInt -> Ptr CInt -> IO CBool

-- | Low-level wrapper around the C function /solver_addclause/.
foreign import ccall unsafe "solver.h solver_simplify"
  cSolverSimplify :: Ptr CSolver -> IO CBool

-- | Low-level wrapper around the C function /solver_solve/.
--   The Ptr C_Lit should be ignored. In the c code, they are just used
--   for printing and also that lines are comment.
--   The return value says iff the calculation finished 
--   (else it got interupted).
foreign import ccall unsafe "solver.h solver_solve"
  cSolverSolve :: Ptr CSolver -> Ptr CInt -> Ptr CInt -> IO CBool

-- | Gives you the number of variables in the solver.
foreign import ccall unsafe "solver.h solver_nvars"
  cSolverNVars :: Ptr CSolver -> IO CInt

-- | Gives you the number of clauses in the solver.
foreign import ccall unsafe "solver.h solver_nclauses"
  cSolverNClauses :: Ptr CSolver -> IO CInt

-- | Gives you the number of clauses in the solver.
foreign import ccall unsafe "solver.h solver_setnvars"
  cSolverSetNVars :: Ptr CSolver -> CInt -> IO ()

foreign import ccall unsafe "solver.h ipasirVal"
  cIpasirVal :: Ptr CSolver -> CInt -> IO CInt

-- lbool solver_search(solver* s, int nof_conflicts, int nof_learnts)
foreign import ccall unsafe "solver.h solver_solution"
  cSolverSolution :: Ptr CSolver -> IO CChar

foreign import ccall unsafe "solver.h solver_copy"
  cCopySolver :: Ptr CSolver -> IO (Ptr CSolver)

cChartoLBool :: CChar -> LBool
cChartoLBool 1 = LTrue
cChartoLBool 0 = LUndef
cChartoLBool _ = LFalse

withSP (HSolver p _ _) = generalizedWithForeignPtr p

class ForeignFunction b where
    generalizedWithForeignPtr :: ForeignPtr a -> (Ptr a -> b) -> b

instance ForeignFunction (IO a) where
    generalizedWithForeignPtr = withForeignPtr

instance (ForeignFunction b) => ForeignFunction (a -> b) where
    generalizedWithForeignPtr s f x = generalizedWithForeignPtr s $ flip f x

instance Ipasir HSolver where
  ipasirGetID (HSolver p _ _) = toEnum $ fromEnum $ ptrToIntPtr $ unsafeForeignPtrToPtr p
  ipasirInit = liftM3 HSolver (newForeignPtr cDelSolverGC =<< cNewSolver) 
                              (newIORef [])
                              (return nullPtr)
  ipasirNumberVars s = withSP s cSolverNVars
  ipasirSolve s@(HSolver p assumptions lastSol) = do
    ass <- readIORef assumptions
    b <- if null ass
      then withSP s cSolverSolution
      else do
        traceM "Haskell 1"
        cs <- withSP s cCopySolver
        traceM "Haskell 2"
        mapM_ (addClause cs . pure) ass 
        traceM "Haskell 3"
        b <- cSolverSolution cs
        traceM "Haskell 4"
        cDelSolver cs
        traceM "Haskell 5"
        writeIORef assumptions []
        traceM "Haskell 6"
        return b
    pure $ case b of
      1 -> LTrue
      0 -> LUndef
      _ -> LFalse
  ipasirAddClause s = withSP s addClause 
  ipasirAssume (HSolver p ass _) a = modifyIORef ass (a:)
  ipasirVal s = withSP s cIpasirVal
  ipasirFailed s i = (/=0) <$> withSP s cIpasirVal i

addClause :: Ptr CSolver -> [CInt] -> IO ()
addClause ptr clause = do
  startPtr <- newArray $ map toLit clause
  let endPtr = advancePtr startPtr $ length clause
  b <- cSolverAddClause ptr startPtr endPtr -- cnf became trivial if b is true
  free startPtr


f1 = ipasirInit :: IO HSolver

f2 = do 
  x <- f1
  ipasirAddClause x [1,-2]
  ipasirAddClause x [2,-3]
  ipasirAddClause x [3,-4]
  ipasirAddClause x [4,-5]
  ipasirAddClause x [5,-1]
  ipasirAssume x (-1)
  return x

f2' = do 
  x <- f2
  ipasirAssume x 4
  return x

f3 = do 
  x <- f1
  ipasirAddClause x [1,-2]
  ipasirAddClause x [-1,-2]
  ipasirAddClause x [2]
  ipasirAddClause x [-1,2]
  return x

f4 = do
  x <- f1
  ipasirAddClause x [1, -3]
  ipasirAddClause x [2,3,-1]
  return x

f5 = do 
  x <- f4
  ipasirAssume x 1
  ipasirAssume x 3
  solveReady x

solveReady x = 
  whileM ((==LTrue) <$> ipasirSolve x) $ do
    sol <- ipasirSolution x
    print sol
    ipasirAddClause x $ head $ negSolutionToEncoding (Proxy :: Proxy (SAT CInt LBool)) sol

unc f x y = do 
  a <- f x 
  b <- f y
  return (a,b)
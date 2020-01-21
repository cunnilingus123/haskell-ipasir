{-# LANGUAGE ForeignFunctionInterface #-}

module SAT.IPASIR.Minisat where

-- | A low-level Haskell wrapper around the MiniSat-All library.

import Foreign
import Foreign.C.Types
import Control.Monad (when)
import Control.Monad.Loops 
import Data.Proxy

import SAT.IPASIR.IpasirApi
import SAT.IPASIR.ComplexityProblemInstances (LBool(..), SAT(..))
import SAT.IPASIR.ComplexityProblem

-- ----------------------------------------------------------------------
-- * Some types

-- | An abstract type for the solver.
data CSolver = CSolver
newtype HSolver = HSolver (Ptr CSolver)

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

foreign import ccall unsafe "solver.h assume_"
  cAssume :: Ptr CSolver -> CInt -> IO ()

cChartoLBool :: CChar -> LBool
cChartoLBool 1 = LTrue
cChartoLBool 0 = LUndef
cChartoLBool _ = LFalse

instance Ipasir HSolver where
  ipasirGetID (HSolver p) = toEnum $ fromEnum $ ptrToIntPtr p
  ipasirInit = HSolver <$> cNewSolver
  ipasirNumberVars (HSolver p) = cSolverNVars p
  ipasirSolve (HSolver p) = do 
    b <- cSolverSolution p
    case b of
      1 -> pure LTrue
      0 -> pure LUndef
      _ -> pure LFalse
  ipasirAddClause s@(HSolver p) clause = do
    cClause <- newArray $ map toLit clause
    b <- cSolverAddClause p cClause $ advancePtr cClause $ length clause
    free cClause
  ipasirAssume (HSolver p) i = cAssume p $ toLit i
  ipasirVal (HSolver p) = cIpasirVal p
  ipasirFailed (HSolver p) i = (/=0) <$> cIpasirVal p i

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
  ipasirAssume x (4)
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
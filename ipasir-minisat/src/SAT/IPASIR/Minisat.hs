{-# LANGUAGE ForeignFunctionInterface #-}

module SAT.IPASIR.Minisat where

import SAT.IPASIR.IpasirApi

-- | A low-level Haskell wrapper around the MiniSat-All library.

import Foreign
import Foreign.C.Types
import Control.Monad (when)

-- ----------------------------------------------------------------------
-- * Some types

-- | An abstract type for the solver.
data CSolver = CSolver
newtype HSolver = HSolver (Ptr CSolver)

-- ----------------------------------------------------------------------
-- * Conversions
toLit :: CInt -> CInt
toLit l = pos + pos + (toEnum . fromEnum) si
  where
    pos = abs l - 1
    si  = l < 0
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

instance Ipasir HSolver where
  ipasirGetID (HSolver p) = toEnum $ fromEnum $ ptrToIntPtr p
  ipasirInit = HSolver <$> cNewSolver
  ipasirNumberVars (HSolver p) = cSolverNVars p
  ipasirSolve (HSolver p) = do
    cSolverSimplify p
    cSolverSolve p nullPtr nullPtr
  ipasirAddClause s@(HSolver p) clause = do
    cClause <- newArray $ map toLit clause
    b <- cSolverAddClause p cClause $ advancePtr cClause $ length clause
    free cClause
    print b
  ipasirAssume (HSolver p) i = undefined
  ipasirVal (HSolver p) i = undefined
  ipasirFailed (HSolver p) i = undefined

f1 = ipasirInit :: IO HSolver

f2 = do 
  x <- f1
  ipasirAddClause x [1,-2]
  ipasirAddClause x [2,-3]
  ipasirAddClause x [3,-4]
  ipasirAddClause x [4,-5]
  ipasirAddClause x [5]
  ipasirAddClause x [-1]
 -- ipasirAddClause x [-1,2]
  return x

f3 = do 
  x <- f1
  ipasirAddClause x [1,-2]
  ipasirAddClause x [-1,-2]
  ipasirAddClause x [2]
  ipasirAddClause x [-1,2]
  return x
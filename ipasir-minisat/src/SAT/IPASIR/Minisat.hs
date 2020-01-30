{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module SAT.IPASIR.Minisat 
  ( CMinisat
  , cminisat
  ) where
    
import Data.Proxy (Proxy(..))
import Data.Array (listArray)
import Data.List (findIndices)
import Foreign (Ptr, ForeignPtr, FinalizerPtr, newForeignPtr, withForeignPtr, newArray, advancePtr, free, ptrToIntPtr)
import Foreign.C.Types (CInt(..), CChar(..), CBool(..))
import Foreign.ForeignPtr.Unsafe (unsafeForeignPtrToPtr)
import System.IO.Unsafe (unsafePerformIO, unsafeInterleaveIO)

--import SAT.IPASIR.Solver(Solver(..), IncrementalSolver(..), incrementalSolution)
import SAT.IPASIR.IpasirApi 
import SAT.IPASIR.ComplexityProblemInstances (LBool(..), SAT(..))

-- ----------------------------------------------------------------------
-- * Some types

-- | An abstract type for the solver.
data CSolver = CSolver
newtype HSolver = HSolver (ForeignPtr CSolver)
type CMinisat = IpasirSolver HSolver
cminisat :: Proxy CMinisat
cminisat = Proxy

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
  cIpasirVal :: Ptr CSolver -> CInt -> IO CChar

-- lbool solver_search(solver* s, int nof_conflicts, int nof_learnts)
foreign import ccall unsafe "solver.h solver_solution"
  cSolverSolution :: Ptr CSolver -> IO CChar

cChartoLBool :: CChar -> LBool
cChartoLBool 1 = LTrue
cChartoLBool 0 = LUndef
cChartoLBool _ = LFalse

withSP (HSolver p) = generalizedWithForeignPtr p

class ForeignFunction b where
    generalizedWithForeignPtr :: ForeignPtr a -> (Ptr a -> b) -> b

instance ForeignFunction (IO a) where
    generalizedWithForeignPtr = withForeignPtr

instance (ForeignFunction b) => ForeignFunction (a -> b) where
    generalizedWithForeignPtr s f x = generalizedWithForeignPtr s $ flip f x

instance Ipasir HSolver where
  ipasirGetID (HSolver p) = toEnum $ fromEnum $ ptrToIntPtr $ unsafeForeignPtrToPtr p
  ipasirInit = HSolver <$> (newForeignPtr cDelSolverGC =<< cNewSolver)
  ipasirNumberVars s = withSP s cSolverNVars
  ipasirSolve s@(HSolver p) = cChartoLBool <$> withSP s cSolverSolution
  ipasirAddClause s clause = do
    startPtr <- newArray $ map toLit clause
    let endPtr = advancePtr startPtr $ length clause
    b <- withSP s cSolverAddClause startPtr endPtr -- cnf became trivial if b is true
    free startPtr
  ipasirVal s v = do
    let a = abs v
    c <- withSP s cIpasirVal a
    return $ a * ccharToCInt c

ccharToCInt :: CChar -> CInt
ccharToCInt 1 = 1
ccharToCInt 0 = 0
ccharToCInt _ = -1

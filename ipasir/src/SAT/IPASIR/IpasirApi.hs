{-# LANGUAGE TypeFamilies #-}

module SAT.IPASIR.IpasirApi where

import Data.Array (Array, array)
import Data.Ix (Ix(..))
import Foreign.C.Types (CInt)
import Control.Monad (forM_)
import System.IO.Unsafe (unsafePerformIO, unsafeInterleaveIO)

import SAT.IPASIR.Solver
import SAT.IPASIR.ComplexityProblemInstances (LBool(..), enumToLBool)
import qualified SAT.IPASIR.ComplexityProblemInstances as CP

type IDType  = Word
type Var     = CInt

instance Ix CInt where
    range (from, to) = [from..to]
    index (from, to) i
      | inRange (from, to) i = fromEnum $ i - from
      | otherwise            = error $ "Index out of bounds Exception. Index:" 
                                        ++ show i ++ " Bounds: " ++ show (from,to)
    inRange (from, to) i = i >= from && i <= to

{-|
    Class that models the <https://github.com/biotomas/ipasir/blob/master/ipasir.h ipasir.h> interface.
    This class is meant to be implemented using foreign function interfaces to the actual C solver.
    In most cases the type @a@ will be a @newtype@ around a 'ForeignPtr'.
    
    A solver can be in different states INPUT, SAT and UNSAT.  Notice, that most functions are not
    state secure. That means: It is not checked if the solver is in 
    a valid state to execute the function and the state doesn\'t update.
-}
class Ipasir a where    
    -- | Every initialized Solver needs a unique ID. The ID is mostly the pointer to the solver.
    ipasirGetID :: a -> IDType

    -- | Returns the number of variables.
    ipasirNumberVars :: a -> IO Var

    -- | Return the name and the version of the incremental @SAT@ solving library.
    ipasirSignature :: a -> IO String
    ipasirSignature solver = return $ "Solver with ID " ++ show (ipasirGetID solver)

    {-|
     Construct a new solver and return a pointer to it.
     Use the returned pointer as the first parameter in each
     of the following functions.

     * Required state: @N/A@
     * State after: @INPUT@

     This function also has to take care of deleding the solver when it gets carbage collected.
     
     Since this function is not state safe it is not checked if the solver is in the required state
     and the solver does not switch to the \"State after\" state from above.
    -}
    ipasirInit :: IO a

    {-|
     Add the given clause.  Clauses added this way
     cannot be removed. The addition of removable clauses
     can be simulated using activation literals and assumptions.

     * Required state: @INPUT@ or @SAT@ or @UNSAT@
     * State after: @INPUT@

     For implementation of this function see 'byIpasirAdd'
    -}
    ipasirAddClause :: a -> [Var] -> IO ()

    {-|
     Add an assumption for the next @SAT@ search (the next call
     of 'ipasirSolve'). After calling 'ipasirSolve' all the
     previously added assumptions are cleared.

     * Required state: @INPUT@ or @SAT@ or @UNSAT@
     * State after: @INPUT@
    -}
    ipasirAssume :: a -> Var -> IO ()

    {-|
     Solve the formula with specified clauses under the specified assumptions.
     If the formula is satisfiable the function returns @LTrue@ and the state of the solver is changed to @SAT@.
     If the formula is unsatisfiable the function returns @LFalse@ and the state of the solver is changed to @UNSAT@.
     If the calculation is interrupted the function returns LUndef. Note @ipasir_set_terminate@ is not supported.
     This function can be called in any defined state of the solver.

     * Required state: @INPUT@ or @SAT@ or @UNSAT@
     * State after: @INPUT@ or @SAT@ or @UNSAT@
    -}
    ipasirSolve :: a -> IO LBool

    {-|
     Get the truth value of the given literal in the found satisfying
     assignment. Return @Pos a@ if True, @Neg a@ if False, and @LUndef@ if not important.
     This function can only be used if ipasirSolve has returned @LTrue@
     and no 'ipasirAdd' nor 'ipasirAssume' has been called
     since then, i.e., the state of the solver is @SAT@.

     * Required state: @SAT@
     * State after: @SAT@
    -}
    ipasirVal :: a -> Var -> IO Var
    
    {-|
     ipasirSolution gives you an 'Array' with the truth value of variable @var@ 
     at index @var@. That means @ipasirSolution@ will make the following function
     returning 'True':
     
      > f s v = do
      >   solution <- ipasirSolution s v
      >   varAt <- ipasirVal s v
      >   return $ solution ! v == varAt

     The second parameter has to indicate the highest variable the SAT solver knows.

     * Required state: @SAT@
     * State after: @SAT@
    -}
    ipasirSolution :: a -> IO (Array Var LBool)
    ipasirSolution solver = do
        maxi <- ipasirNumberVars solver
        let sol = array (1,maxi) [ (var, enumToLBool <$> ipasirVal solver var) | var <- [1..maxi]]
        sequence sol
    
    {-|
     Check if the given assumption literal was used to prove the
     unsatisfiability of the formula under the assumptions
     used for the last @SAT@ search. Return @True@ if so, @False@ otherwise.
     This function can only be used if 'ipasirSolve' has returned @LFalse@ and
     no 'ipasirAdd' or 'ipasirAssume' has been called since then, i.e.,
     the state of the solver is @UNSAT@.

     * Required state: @UNSAT@
     * State after: @UNSAT@
    -}
    ipasirFailed :: a -> Var -> IO Bool
    
    {-|
      Returns every variable, which was involved in the found conflict. The returned
      vector is sorted and distinct. It holds that
      
      @ elem i (ipasirConflict' s) == ipasirFailed' s i -- ignored the IO-monad  @
      
      * Required state: @UNSAT@
      * State after: @UNSAT@
    -}
    ipasirConflict :: a -> IO [Var]
    ipasirConflict solver = do
        maxi <- ipasirNumberVars solver
        filter (/=0) <$> sequence (ipasirConflict' maxi 1)
        where
            ipasirConflict' :: Var -> Var -> [IO Var]
            ipasirConflict' maxi i 
                | i > maxi  = []
                | otherwise = (replaceFalse i <$> ipasirFailed solver i) : ipasirConflict' maxi (succ i)
            replaceFalse :: Num e => e -> Bool -> e
            replaceFalse _ False = 0
            replaceFalse x _     = x

{-|
    byIpasirAdd creates a 'ipasirAddClause' function using an
    ipasirAdd function. That ipasirAdd function has the
    the following documentation:

    Add the given literal into the currently added clause
    or finalize the clause with a 0.  Clauses added this way
    cannot be removed. The addition of removable clauses
    can be simulated using activation literals and assumptions.

    * Required state: @INPUT@ or @SAT@ or @UNSAT@
    * State after: @INPUT@

    Literals are encoded as (non-zero) integers as in the
    DIMACS formats.  They have to be smaller or equal to
    INT_MAX and strictly larger than INT_MIN (to avoid
    negation overflow).  This applies to all the literal
    arguments in API functions.
        
    Notice, that it is not checked
    if the list contains 0 (which starts a new clause). 
    Better avoid every 0 in the list.
-}
byIpasirAdd :: (a -> Var -> IO ()) -> a -> [Var] -> IO ()
byIpasirAdd ipasirAdd solver l = do
    ipasirAdd solver `mapM_` l
    ipasirAdd solver 0

-- | This datatype makes an instance of 'Ipasir' to an instance of 'IncrementalSolver'.
newtype IpasirSolver i = IpasirSolver i

-- | The complexity problem of an instance of Ipasir' is always 'CP.SAT' 'CInt' 'CP.LBool'
type IpasirCP = CP.SAT Var CP.LBool

instance (Ipasir i) => Solver (IpasirSolver i) where
    type CPS (IpasirSolver i) = IpasirCP
    solution = incrementalSolution

instance (Ipasir i) => IncrementalSolver (IpasirSolver i) where
    type MonadIS (IpasirSolver i) = IO
    newIterativeSolver = IpasirSolver <$> ipasirInit
    addEncoding (IpasirSolver ip) sat = do
        forM_ sat $ ipasirAddClause ip
        return $ IpasirSolver ip
    solve = solving $ \ip -> ipasirSolution ip
    assume (IpasirSolver ip) ass = IpasirSolver ip <$ ipasirAssume ip ass
    unwrapMonadForNonIterative _  = unsafePerformIO
    interleaveMonad _ = unsafeInterleaveIO

solving :: Ipasir t => (t -> IO b) -> IpasirSolver t -> IO (Either [Var] b)
solving satCase (IpasirSolver ip) = do
    b <- ipasirSolve ip
    case b of
        LFalse -> Left <$> ipasirConflict ip 
        LUndef -> error $ "The solver returned LUndef on a solving process.\n" ++
                          "This can happen if you terminate the solver by using " ++
                          "ipasir_set_terminate (see ipasir.h)\n" 
        LTrue  -> Right <$> satCase ip

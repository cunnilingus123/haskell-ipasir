{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

module SAT.IPASIR.TestingSuite where

import Test.QuickCheck.Arbitrary (Arbitrary(..))
import Test.QuickCheck.Gen (Gen, elements, choose, vectorOf, listOf)
import Test.QuickCheck (Property, generate)
import Data.Proxy (Proxy (..))
import Control.Monad (liftM2, zipWithM, guard)
import Data.List (sort, nub, tails, (\\), intercalate)
import Data.Reflection (Reifies(..))
import Data.Maybe (mapMaybe)
import Data.Array (Array(..), assocs, (!))
import Data.Ix (Ix(..))

import SAT.IPASIR.Solver
import SAT.IPASIR.SAT (SAT)
import SAT.IPASIR.ComplexityProblem
    ( ComplexityProblem(..)
    , Result
    , Solutiontransform(..)
    , AssumingProblem(..)
    )

createAssumingTest  :: forall s cp a r m t.
               ( AssumingSolver s
               , Show r
               , cp ~ CPS s
               , a ~ Assumption cp
               , r ~ Result cp
               , m ~ MonadIS s
               ) 
            => Proxy s -> ([cp] -> [a] -> r -> Bool) -> ProgramS t cp a  -> Bool
createAssumingTest s validate (ProgramS (Program coms))
    = unwrapSolverMonad s $ looper assume validate [] [] coms

createIncrementalTest :: forall s cp a r m t.
               ( IncrementalSolver s
               , Show r
               , cp ~ CPS s
               , r ~ Result cp
               , m ~ MonadIS s
               ) 
            => Proxy s -> ([cp] -> [a] -> r -> Bool) -> ProgramS t cp a  -> Bool
createIncrementalTest s validate (ProgramS (Program coms))
    = unwrapSolverMonad s $ looper assume' validate [] [] coms
  where
    assume' _ = error "this solver can't assume."

looper :: forall s cp a r. 
    ( IncrementalSolver s
    , cp ~ CPS s
    , r ~ Result cp
    ) => (a -> SolverMonad s ()) -> ([cp] -> [a] -> r -> Bool) -> [cp] -> [a] -> [Command cp a] -> SolverMonad s Bool
looper assume' validate encs assp []            = pure True 
looper assume' validate encs assp (SolveNow:xs) = do
    res <- solve
    l'  <- interleaveSolverMonad (Proxy :: Proxy s) $ looper assume' validate encs [] xs
    return $ validate encs assp res && l'
looper assume' validate encs assp (AddEncoding e : xs) = do
    addEncoding e
    looper assume' validate (e:encs) assp xs 
looper assume' validate encs assp (AssumeSomething a : xs) = do
    assume' a
    looper assume' validate encs (a:assp) xs

checkSatSolution :: forall e b. (ComplexityProblem (SAT e b), Num e, Ord e, Ix e, Eq b) 
                 => b -> b -> [[e]] -> Array e b -> Bool
checkSatSolution f t encoding solution = all checkC encoding 
  where
    checkC clause = any check clause || trivialClause clause
    trivialClause clause = or $ do
        (h:t) <- init (tails clause)
        return $ negate h `elem` t
    check lit
      | lit < 0   = solution ! abs lit == f
      | otherwise = solution !     lit == t

checkSatResult :: forall e b. (ComplexityProblem (SAT e b), Num e, Ord e, Ix e, Eq b) 
                 => b -> b -> [[e]] -> Result (SAT e b) -> Bool
checkSatResult f t enc Nothing  = True
checkSatResult f t enc (Just s) = checkSatSolution f t enc $ error "Should be 'checkSatSolution f t enc s', but this function doesnt work for different literal types right now" 

checkSatEncsAssumpt :: forall e b. (ComplexityProblem (SAT e b), Num e, Ord e, Ix e, Eq b) 
                 => b -> b -> [[[e]]] -> [e] -> Result (SAT e b) -> Bool
checkSatEncsAssumpt f t encs assumps = checkSatResult f t (map pure assumps ++ concat encs)

data AssumptionRestriction 
    = NoAssumption 
    | SingleAssumtionBeforeSolve
    | MultiAssumptionBeforeSolve
    | NoAssumptionRestriction
    deriving (Show, Eq, Ord, Enum)

data VariableUsageRestriction
    = EveryVarUsed
    | MaxVarUsed
    | NoEncodingRestriction
    deriving (Show, Eq, Ord, Enum)

data ClausesRestriction
    = NormalClause
    | RandomLits
    deriving (Show, Eq, Ord, Enum)

data CommandMarker
    = AddEncodingMarker
    | CompleteEncodingMarker
    | AssumeSomethingMarker
    | SolveNowMarker
    deriving (Show, Eq, Ord, Enum)

data Command enc ass
    = AddEncoding enc
    | AssumeSomething ass
    | SolveNow
    deriving (Show, Eq, Ord)

newtype Program enc ass = Program [Command enc ass]
    deriving (Show, Eq, Ord)
newtype ProgramS s enc ass = ProgramS (Program enc ass)

unreflectProgram :: Proxy s -> ProgramS s enc ass -> Program enc ass
unreflectProgram _ (ProgramS p) = p

instance Show (Command enc ass) => Show (ProgramS s enc ass) where
    show (ProgramS (Program coms)) = "-- ProgramS --\n" ++ intercalate "\n" (map show coms)

data RefiedArbitrary enc ass = RefiedArbitrary (Gen enc) (Gen ass) ([enc] -> enc) Word AssumptionRestriction

createSatArbitrary :: forall e. (Enum e, Num e, Eq e)
                   => Word 
                   -> Word 
                   -> AssumptionRestriction
                   -> VariableUsageRestriction 
                   -> ClausesRestriction
                   -> RefiedArbitrary [[e]] e
createSatArbitrary nVar nSolvings aRestr vRestr cRestr
    = RefiedArbitrary (genEncoding cRestr) litGen (completeEncoding vRestr) nSolvings aRestr
  where
    genEncoding RandomLits = listOf $ listOf litGen
    genEncoding _          = listOf $ 
        filter (/=0) . zipWith (*) [1..maxLit] <$> vectorOf maxLitInt (elements [-1,0,1])
    litGen :: Gen e
    litGen = do
        l <- choose (negate maxLitInt + 1, maxLitInt)
        let lit = case l of
                0 -> negate maxLitInt
                x -> x
        return $ toEnum lit
    maxLitInt = fromEnum nVar :: Int
    maxLit = toEnum maxLitInt :: e
    vars :: [[[e]]] -> [e]
    vars = map abs . concat .  concat 
    completeEncoding :: VariableUsageRestriction -> [[[e]]] -> [[e]]
    completeEncoding EveryVarUsed          = filter (not . null) . pure . ([1..maxLit] \\) . vars
    completeEncoding MaxVarUsed            = pure . (maxLit <$) . guard . notElem maxLit . vars
    completeEncoding NoEncodingRestriction = const []

instance (Reifies s (RefiedArbitrary enc ass)) => Arbitrary (ProgramS s enc ass) where
    arbitrary = genProgram ra
      where
        ra = reflect (Proxy :: Proxy s)

genProgram :: forall s enc ass. RefiedArbitrary enc ass -> Gen (ProgramS s enc ass)
genProgram (RefiedArbitrary encoding assumption completer n restr) = do
    block <- genCommandBlock n restr
    ProgramS . Program <$> parser block []
  where
    parseCommand :: CommandMarker -> Gen (Command enc ass) -- Partial function !!! Use parser.
    parseCommand AddEncodingMarker     = AddEncoding     <$> encoding
    parseCommand AssumeSomethingMarker = AssumeSomething <$> assumption
    parseCommand SolveNowMarker        = return SolveNow
    parser :: [CommandMarker] -> [Command enc ass] -> Gen [Command enc ass]
    parser (CompleteEncodingMarker:xs) past = do
        rest <- mapM parseCommand xs
        let c = AddEncoding $ completer $ mapMaybe toEncoding past
        return $ reverse past ++ c : rest
    parser (x:xs) past = parser xs . (:past) =<< parseCommand x
    parser _      past = pure $ reverse past
    toEncoding :: Command enc ass -> Maybe enc
    toEncoding (AddEncoding e) = Just e
    toEncoding _ = Nothing

genCommandBlock :: Word -> AssumptionRestriction -> Gen [CommandMarker]
genCommandBlock n restr = do
    t <- sequence $ arbitrary <$ [0..n-1]
    s <- zipWithM (f restr) t [0..]
    pure $ resorting =<< s
  where
    assOrAdd :: Gen CommandMarker
    assOrAdd = elements [AssumeSomethingMarker, AddEncodingMarker]
    f :: AssumptionRestriction -> Word -> Word -> Gen [CommandMarker]
    f _ 0 0 = pure [CompleteEncodingMarker, SolveNowMarker]
    f _ 0 _ = pure [SolveNowMarker]
    f SingleAssumtionBeforeSolve 1 m = fmap sort $ liftM2 (:) assOrAdd $ f SingleAssumtionBeforeSolve 0 m
    f r n m = do
        c <- if r <= SingleAssumtionBeforeSolve
            then pure AddEncodingMarker
            else assOrAdd
        (c:) <$> f r (n-1) m
    resorting :: [CommandMarker] -> [CommandMarker]
    resorting 
        | restr == MultiAssumptionBeforeSolve = sort
        | otherwise = id

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Data.Proxy(Proxy(..))
import Data.Reflection
import Test.QuickCheck
import Foreign.C.Types

import Test.Tasty
import Test.Tasty.QuickCheck

import SAT.IPASIR.TestingSuite
import SAT.IPASIR.Minisat
import SAT.IPASIR.ComplexityProblemInstances
import SAT.IPASIR.Solver

main :: IO ()
main = defaultMain testTree

testTree :: TestTree
testTree = testGroup "Testing Minisat" 
           [-- f "Easy way" easy
          -- , f "multi Solve" multi
          -- , f "All But Assume 1" allButAssume1
          -- , f "All But Assume 2" allButAssume2
            f "assuming easy" assu
           ]

easy = createSatArbitrary 8 1 NoAssumption EveryVarUsed NormalClause
multi = createSatArbitrary 8 3 NoAssumption EveryVarUsed NormalClause
allButAssume1 = createSatArbitrary 12 3 NoAssumption NoEncodingRestriction RandomLits
allButAssume2 = createSatArbitrary 12 3 NoAssumption NoEncodingRestriction NormalClause
assu = createSatArbitrary 7 1 SingleAssumtionBeforeSolve EveryVarUsed NormalClause

unreflectF :: Proxy s -> (ProgramS s a b -> c) -> (Program a b -> c)
unreflectF _ f = f . ProgramS

unreflectF2 :: Proxy s -> ((ProgramS s a b -> c) -> d) -> (ProgramS s a b -> c) -> d
unreflectF2 _ = id

test1 :: ProgramS s [[CInt]] CInt -> Bool
test1 = createTest (Proxy :: Proxy CMinisat) $ checkSatEncsAssumpt LFalse LTrue

f :: String -> RefiedArbitrary [[CInt]] CInt -> TestTree
f name easy = reify easy $ \p -> unreflectF2 p (testProperty name) test1

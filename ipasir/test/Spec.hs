
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

import Data.Proxy(Proxy(..))
import Data.Reflection
import Data.List.Split
import qualified Data.Map
import qualified Data.Array
import Data.Bifunctor (first, second)
import Test.QuickCheck
import Foreign.C.Types
import Control.Applicative ( Applicative(liftA2) ) 
import Data.List.Ordered (nubSort)
import Data.Bifoldable
import Data.Word

import Test.Tasty
import Test.Tasty.QuickCheck

import SAT.IPASIR.Formula
import SAT.IPASIR.SAT
import SAT.IPASIR.XSAT
import SAT.IPASIR.LBool
import SAT.IPASIR.Literals ( Lit(..), ByNumber(ByNumber), Literal(unsign, lit), litSatisfied )
import SAT.IPASIR.ComplexityProblem

import Debug.Trace

main :: IO ()
main = defaultMain testTree

testTree :: TestTree
testTree = testGroup "Testing CP" 
    [ checkSolutiontransform
    , checkReductions (Proxy :: Proxy  SAT) SatToXSatRed
    , checkReductions (Proxy :: Proxy XSAT) XSatToSatRed
    ]

numVars = 50

instance Arbitrary (SAT (ByNumber Int) b) where
    arbitrary = SAT <$> listOf (listOf arbitrary)
    shrink (SAT cnf) = SAT <$> shrink' cnf

instance (Arbitrary v, Ord v) => Arbitrary (Lit v) where
    arbitrary = liftA2 lit arbitrary arbitrary

instance Arbitrary (ByNumber Int) where
    arbitrary = do
        i <- choose (1-numVars, numVars)
        return $ ByNumber $ if i == 0 then -numVars else i

instance (Arbitrary v, Ord v) => Arbitrary (SAT (Lit v) b) where
    arbitrary = SAT <$> listOf (listOf arbitrary)
    shrink (SAT cnf) = SAT <$> shrink' cnf

instance Arbitrary b => Arbitrary (XSAT (ByNumber Int) b) where
    arbitrary = liftA2 XSAT (listOf (listOf arbitrary)) 
                            (listOf (take 5 <$> listOf arbitrary))
    shrink (XSAT cnf xnf) = [XSAT cnf' xnf | cnf' <- shrink' cnf] ++ [XSAT cnf xnf' | xnf' <- shrink' xnf]

instance (Arbitrary v, Ord v) => Arbitrary (XSAT (Lit v) b) where
    arbitrary = liftA2 XSAT (listOf (listOf arbitrary)) 
                            (take 16 <$> listOf (take 8 <$> listOf arbitrary))
    shrink (XSAT cnf xnf) = [XSAT cnf' xnf | cnf' <- shrink' cnf] ++ [XSAT cnf xnf' | xnf' <- shrink' xnf]

instance Arbitrary LBool where
    arbitrary = elements [LFalse, LUndef, LTrue]
    shrink x  = [ LTrue | x == LUndef ]

instance Arbitrary b => Arbitrary (Data.Array.Array Int b) where
    arbitrary = Data.Array.listArray (1,numVars) <$> infiniteList

--shrink' :: SAT e b -> [SAT e b]
shrink' cnf
    =  [cnf' | length cnf > 20, cnf' <- chunksOf 20 cnf]
    ++ [tail cnf | not $ null cnf]
    ++ [map safeTail cnf | not $ null $ concat cnf]
    where
        safeTail [] = []
        safeTail (_:xs) = xs

createAssignmentLit :: (Ord v, Arbitrary b) => SAT (Lit v) b -> Gen (Data.Map.Map v b)
createAssignmentLit (SAT cnf) = Data.Map.fromList . zip allVars <$> infiniteList
    where allVars = nubSort $ unsign <$> concat cnf

checkSolutiontransform :: TestTree
checkSolutiontransform = testGroup "check Instances"
    [   testGroup "Testing Solutiontransform <-> NPProblem" 
        [   testGroup "Int" 
            [ testProperty "checkModel assignment (solutionToEncoding    assignment) == True"  $ \assignment -> checkModel assignment (solutionToEncoding assignment :: SAT (ByNumber Int) Bool)
            , testProperty "checkModel assignment (negSolutionToEncoding assignment) == False" $ \assignment -> not $ checkModel assignment (negSolutionToEncoding assignment :: SAT (ByNumber Int) Bool)
            , testProperty "a1 /= a2 ==> checkModel a1 (   solutionToEncoding a2)    == False" $ \a1 a2 -> (a1 == a2) == checkModel a2 (solutionToEncoding a1 :: SAT (ByNumber Int) Bool)
            , testProperty "a1 /= a2 ==> checkModel a1 (negSolutionToEncoding a2)    == True"  $ \a1 a2 -> (a1 == a2) /= checkModel a2 (negSolutionToEncoding a1 :: SAT (ByNumber Int) Bool)
            ]
        ,   testGroup "Lit" 
            [ testProperty "checkModel assignment (solutionToEncoding    assignment) == True"  $ \assignment -> checkModel assignment (solutionToEncoding assignment :: SAT (Lit Char) Bool)
            , testProperty "checkModel assignment (negSolutionToEncoding assignment) == False" $ \assignment -> not (checkModel assignment (negSolutionToEncoding assignment :: SAT (Lit Char) Bool))
            , testProperty "a1 /= a2 ==> checkModel a1 (   solutionToEncoding a2)    == False" $ \a1 a2 -> Data.Map.isSubmapOfBy (==) a1 a2 == checkModel a2 (solutionToEncoding a1 :: SAT (Lit Char) Bool)
            , testProperty "a1 /= a2 ==> checkModel a1 (negSolutionToEncoding a2)    == True"  $ \a1 a2 -> null (Data.Map.filter not (Data.Map.intersectionWith (==) a1 a2)) /= checkModel a2 (negSolutionToEncoding a1 :: SAT (Lit Char) Bool)
            ]
        ]
    ,   testGroup "Bifoldable" 
        [   testProperty "bifoldr is correct on (:)" $ \s sat@(SAT cnf :: SAT (Lit Char) Bool) -> bifoldr (:) undefined s sat == foldr (:) s (concat cnf)
        ,   testProperty "bifoldl is correct on (+)" $ \s sat@(SAT cnf :: SAT (ByNumber Int) Bool) -> bifoldl (+) undefined s sat == foldl (+) s (concat cnf)
        ]
    ]

checkReduction :: 
    ( Reduction r
    , Show r
    , Arbitrary (CPFrom r)
    , Arbitrary (Solution (CPTo r))
    , Show (CPFrom r)
    , Show (Solution (CPTo r))
    , NPProblem (CPFrom r)
    , NPProblem (CPTo r)
    ) => String -> r -> TestTree
checkReduction s reduction = testProperty s $ \c assignment -> checkModel (parseSolution reduction assignment) c == checkModel assignment (fst (parseEncoding reduction c))

checkReductions :: forall (r :: * -> *) (cp :: * -> * -> *) r1 r2 r3 r4.
    ( r1 ~ r (cp (ByNumber Int) Bool)
    , r2 ~ r (cp (ByNumber Int) LBool)
    , r3 ~ r (cp (Lit Word8) Bool)
    , r4 ~ r (cp (Lit Word8) LBool)
    , Reduction r1
    , Reduction r2
    , Reduction r3
    , Reduction r4
    , Show r1
    , Show r2
    , Show r3
    , Show r4
    , Arbitrary (CPFrom r1)
    , Arbitrary (CPFrom r2)
    , Arbitrary (CPFrom r3)
    , Arbitrary (CPFrom r4)
    , Arbitrary (Solution (CPTo r1))
    , Arbitrary (Solution (CPTo r2))
    , Arbitrary (Solution (CPTo r3))
    , Arbitrary (Solution (CPTo r4))
    , Show (CPFrom r1)
    , Show (CPFrom r2)
    , Show (CPFrom r3)
    , Show (CPFrom r4)
    , Show (Solution (CPTo r1))
    , Show (Solution (CPTo r2))
    , Show (Solution (CPTo r3))
    , Show (Solution (CPTo r4))
    , NPProblem (CPFrom r1)
    , NPProblem (CPFrom r2)
    , NPProblem (CPFrom r3)
    , NPProblem (CPFrom r4)
    , NPProblem (CPTo r1)
    , NPProblem (CPTo r2)
    , NPProblem (CPTo r3)
    , NPProblem (CPTo r4)
    ) => Proxy cp -> (forall l b. r (cp l b)) -> TestTree
checkReductions _ f = testGroup "CP is satisfied <=> Reduced CP is satisfied"
    [ checkReduction "Int  Bool" (f :: r1)
    , checkReduction "Int LBool" (f :: r2)
    , checkReduction "(Lit Char)  Bool" (f :: r3)
    , checkReduction "(Lit Char) LBool" (f :: r4)
    ]

model :: Data.Array.Array Int LBool
model = Data.Array.array (1,2) [(1, LTrue), (2, LUndef)]
enc :: XSAT (ByNumber Int) LBool
enc   = XSAT [] [[1,2]]


cm sol (XSAT cnf xnf) = map (map (litSatisfied sol)) xnf

xsat :: Gen (XSAT (Lit Word8) Bool)
xsat = arbitrary

tt :: IO Bool
tt = generate $ liftA2 checkModel arbitrary xsat

--sat :: IO Bool
sat = generate $ do
 --   ass <- arbitrary
    enc <- xsat
    return $ first (const enc) $ parseEncoding (XSatToSatRed :: XSatToSatRed (XSAT (Lit Word8) Bool)) enc


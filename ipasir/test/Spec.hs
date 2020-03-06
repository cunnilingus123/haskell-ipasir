{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}

import Data.Proxy(Proxy(..))
import Data.Reflection
import Data.Map (Map, fromList)
import Data.Bifunctor (second)
import Test.QuickCheck
import Foreign.C.Types

import Test.Tasty
import Test.Tasty.QuickCheck

import SAT.IPASIR.Formula
import SAT.IPASIR.LBool
import SAT.IPASIR.Literals
import SAT.IPASIR.ComplexityProblem

main :: IO ()
main = defaultMain testTree

testTree :: TestTree
testTree = testGroup "Testing CP" 
    [ testGroup "Test simplifyFormula" 
        [ testProperty "equivalence" $ \f (Model m) -> 
            checkFormula m (unLit =<< simplifyFormula f) == checkFormula m f
        , testProperty "other Properties" $ simplifyFormulaTests . simplifyFormula
        ]
    ]

instance Arbitrary (CSATLit Int b) where
    arbitrary = CSATLit <$> arbitrary

instance Arbitrary (Formula Int) where
    arbitrary = do
        numVars <- choose (1,100)
        sized (randomFormula numVars)

newtype Model = Model (Map Int LBool) 
    deriving (Show)

instance Arbitrary Model where
    arbitrary = do
        i <- choose (0,3^100 - 1) :: Gen Integer
        let f :: Integer -> [LBool]
            f 0 = repeat LUndef
            f i = parseEnum (mod i 3 - 1) : f (div i 3)
        return $ Model $ fromList $ zip [1..] $ take 100 $ f i

parseEnum = toEnum . fromEnum

randomFormula :: Int -> Int -> Gen (Formula Int)
randomFormula numVars 0 = do
    i <- choose (-1,numVars) :: Gen Int
    return $ case i of
        (-1) -> No
        0    -> Yes
        _    -> Var i
randomFormula numVars size = do 
    i <- choose (1,4) :: Gen Int
    if i == 1 
        then Not <$> randomFormula numVars (size-1)
        else do
            let operator = [All, Some, Odd] !! (i-2)
            kSummands <- choose (1,size)
            sizes <- randomSummands size kSummands
            innerFormulas <- sequence $ randomFormula numVars <$> sizes
            return $ operator innerFormulas

randomSummands :: Int -> Int -> Gen [Int]
randomSummands n 1 = return [n]
randomSummands n k = do
    x <- choose (0,n)
    (x :) <$> randomSummands (n-x) (k-1)

simplifyFormulaTests :: Formula (Lit Int) -> Bool
simplifyFormulaTests Yes = True
simplifyFormulaTests No  = True
simplifyFormulaTests f   = go f
    where
        go Yes     = False
        go No      = False
        go (Not _) = False
        go (Var _) = True
        go f       = length l >= 2 && all go l 
            where
                l = innerFormulas f

checkFormula :: Map Int LBool -> Formula Int -> Bool
checkFormula m f = checkModel m (CSATLit f :: CSATLit Int LBool)

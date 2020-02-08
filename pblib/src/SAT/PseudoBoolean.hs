{-# LANGUAGE RankNTypes #-}

module SAT.PseudoBoolean
    ( encodeAMO
    , encodeAMK
    , encodeALK
    , encodeBetween
    , firstAuxiliaryVar
    , WeightedLit(..)
    , ($-$)
    , weightedLit
    , defaultConfig
    , Config (..)
    , AMO_ENCODER(..)
    , AMK_ENCODER(..)
    , PB_ENCODER(..)
    , BimanderMIs(..)
    , CardinalityMonad
    , evalEncoder
    , encodeNewGeq
    , encodeNewLeq
    , getClauses
    , aboveLimited
    , belowLimited
    , bothLimited 
    , addConditional
    , clearConditionals
    , clearDB
    ) where

import SAT.PseudoBoolean.CardinalityMonad
import SAT.PseudoBoolean.Config
import SAT.PseudoBoolean.WeightedLit

import System.IO.Unsafe (unsafePerformIO)

-- | Gives a SAT encoding for __at most one__ literal is true.
--   This function will create auxiliary variables starting at
--   the given Int (third parameter).
--   Make sure the first auxiliary valiable is higher then every
--   absolute of the lits. You can use 'firstAuxiliaryVar' for that.
--   In case the
--   __l__ is of type 'WeightedLit', the function works in respect the the weight. 
encodeAMO :: WLit l => Config -> [l] -> Int -> [[Int]]
encodeAMO config lits = encodeAMK config lits 1

-- | Gives a SAT encoding for __at most k__ literals are true. In case the
--   __l__ is of type 'WeightedLit', the function works in respect the the weight. 
encodeAMK :: WLit l => Config -> [l] -> Int -- ^ k (upper bound)
                                     -> Int -- ^ first auxiliary valiable
                                     -> [[Int]]
encodeAMK = compareK aboveLimited

-- | Same as 'encodeAMK' but it encodes __at least k__. 
encodeALK :: WLit l => Config -> [l] -> Int -- ^ k (lower bound)
                                     -> Int -- ^ first auxiliary valiable
                                     -> [[Int]]
encodeALK = compareK belowLimited

-- | Like 'encodeAMK' and 'encodeALK' together. The first int in the tuple
--   stands for the lower bound and the second one stands for the upper bound.
encodeBetween :: WLit l => Config -> [l] -> (Int,Int) -> Int -> [[Int]]
encodeBetween = compareK bothLimited

-- | Gives the first possible auxiliary variable. That means the result is
--   the smallest possitive int, which is higher than every absolute of the
--   given literals.
firstAuxiliaryVar :: WLit l => [l] -> Int
firstAuxiliaryVar = succ . maximum . map (abs . fromEnum . literal . weightit)

compareK :: (BoundsOK lb ub t, WLit l) => CardinalityMonad lb ub a -> Config -> [l] -> t -> Int -> a
compareK m config lits max firstFree = unsafePerformIO $ evalEncoder config lits max firstFree m

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

module SAT.IPASIR.VarCache
    ( VarCacheOrd (VarCacheOrd)
    , VarCacheIntegral (VarCacheIntegral)
    , GeneralVarCache (GeneralVarCache)
    , VarCache 
        ( addVarsToCache
        , unsafeIntegralToVar
        , integralToVar
        , varToIntegral
        , mapArrayOnMap
        )
    ) where

import qualified Data.Vector as Vec
import qualified Data.Array
import qualified Data.Map
import Data.Vector (Vector, (!), (!?))
import Data.Bifunctor (first)
import Data.List.Ordered (nubSort, minus)
import Control.Applicative ( Alternative((<|>)) )

newtype VarCacheOrd a = VarCacheOrd [Vector a]

data VarCacheIntegral a = VarCacheIntegral

data GeneralVarCache a = forall c. VarCache c a => GeneralVarCache (c a)

class VarCache (c :: * -> *) a where 
    addVarsToCache :: [a] -> c a -> c a
    unsafeIntegralToVar :: Integral i => c a -> i -> a
    integralToVar :: Integral i => c a -> i -> Maybe a
    varToIntegral :: Integral i => c a -> a -> Maybe i
    mapArrayOnMap :: (Data.Array.Ix i, Integral i) => c a -> Data.Array.Array i b -> Data.Map.Map a b

binarySearch :: Ord a => Vector a -> a -> Maybe Int
binarySearch vec x = go 0 $ Vec.length vec - 1
    where
        go l r = case (compare x (vec ! m), l < r) of
            (EQ, _)    -> Just m
            (_, False) -> Nothing
            (LT, _)    -> go l (m - 1)
            (GT, _)    -> go (m + 1) r
            where m = div (l + r) 2

instance Ord a => VarCache VarCacheOrd a where
    addVarsToCache l (VarCacheOrd vc) = addVarsToCache' sortedVector vc
        where
            sortedVector = nubSort l

            addVarsToCache' :: Ord a => [a] -> [Vector a] -> VarCacheOrd a
            addVarsToCache' l []
                | null l = VarCacheOrd []
                | otherwise      = VarCacheOrd [Vec.fromList l]
            addVarsToCache' l [vc]
                | null low = VarCacheOrd [vc']
                | otherwise        = VarCacheOrd [vc', Vec.fromList low]
                where
                    (low, high) = go l $ Vec.toList vc
                    vc'         = vc <> Vec.fromList high
                    go :: Ord a => [a] -> [a] -> ([a],[a])
                    go    []   _     = ([],[])
                    go    xs   []    = ([],xs)
                    go (x:xs) (y:ys) = case compare x y of
                        LT -> first (x :) $ go xs (y:ys)
                        GT -> go (x:xs) ys
                        EQ -> go xs ys
            addVarsToCache' l (x:xs) = addVarsToCache' l' xs
                where l' = minus l $ Vec.toList x
    unsafeIntegralToVar (VarCacheOrd vc) i = go vc $ fromIntegral (i-1)
        where
            go (x:xs) i 
                | i < Vec.length x = x ! i 
                | otherwise        = go xs (i - Vec.length x)
    integralToVar (VarCacheOrd vc) i
        | i > 0 && i' <= sum (map Vec.length vc) = Just $ unsafeIntegralToVar (VarCacheOrd vc) i
        | otherwise                              = Nothing
        where i' = fromIntegral i
    varToIntegral (VarCacheOrd vc) a = fromIntegral <$> go vc a 1
        where
            go :: Ord a => [Vector a] -> a -> Int -> Maybe Int
            go []     _ _ = Nothing
            go (x:xs) a c = fmap (+c) (binarySearch x a) 
                                    <|> go xs a (Vec.length x + c)
    mapArrayOnMap (VarCacheOrd vc) arr = intoMap vc' bs
        where
            a  = pred $ fromIntegral $ fst $ Data.Array.bounds arr
            bs = drop (negate a) $ Data.Array.elems arr
            vc' = go vc a
                where
                    go (x:xs) a
                        | a < Vec.length x = Vec.drop a x : xs
                        | otherwise        = go xs (a - Vec.length x)
            intoMap :: Ord a => [Vector a] -> [b] -> Data.Map.Map a b
            intoMap []     _  = Data.Map.empty
            intoMap (x:xs) bs = m `Data.Map.union` intoMap xs (drop len bs)
                where
                    len = Vec.length x
                    m   = Data.Map.fromAscList $ zip (Vec.toList x) bs

instance (Integral a) => VarCache VarCacheIntegral a where
    addVarsToCache _ _ = VarCacheIntegral
    unsafeIntegralToVar _ i = fromIntegral i
    integralToVar _ i 
        | i > 0     = Just $ fromIntegral i
        | otherwise = Nothing
    varToIntegral _ a = Just $ fromIntegral a
    mapArrayOnMap _ arr = Data.Map.fromAscList $ map (first fromIntegral) $ Data.Array.assocs arr

instance VarCache GeneralVarCache a where
    addVarsToCache l (GeneralVarCache c)    = GeneralVarCache $ addVarsToCache l c
    unsafeIntegralToVar (GeneralVarCache c) = unsafeIntegralToVar c
    integralToVar (GeneralVarCache c)       = integralToVar c
    varToIntegral (GeneralVarCache c)       = varToIntegral c
    mapArrayOnMap (GeneralVarCache c)       = mapArrayOnMap c

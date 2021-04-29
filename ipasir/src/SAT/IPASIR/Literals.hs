{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}

module SAT.IPASIR.Literals
    ( Literal (..)
    , Lit (Neg, Pos)
    , ByNumber(ByNumber)
    , fromBool
    , integralToLit
    , litToIntegral
    , litSatisfied
    , isNegative
    ) where

import SAT.IPASIR.VarCache
    ( VarCacheIntegral(VarCacheIntegral)
    , VarCacheOrd(VarCacheOrd)
    , GeneralVarCache(..)
    , VarCache(varToIntegral, integralToVar, mapArrayOnMap) 
    )
import SAT.IPASIR.LBool (BoolLike(ltrue, lfalse, boolToBoolLike), LBool(..))

import Data.Bifunctor (Bifunctor (bimap, first))
import Data.Proxy (Proxy(Proxy))
import Data.Ix (Ix, inRange)
import Control.Monad (ap)

import qualified Data.Map
import qualified Data.Array

-- | > isPositive . neg = not . isPositive
--   > isPositive (setSign b lit) = b
class (Functor (Allocation l), Ord (Variable l)) => Literal l where
    type Variable l
    type HelperLiteral l
    type Allocation l :: * -> *

    -- | Negates a literal.
    neg :: l -> l
    -- | Gets the sign of a 'Literal' ('True' for positive).
    isPositive :: l -> Bool
    -- | Makes the 'Literal' being positive if 'True' und negative if 'False'. The Variable is not changed.
    setSign :: Bool -> l -> l
    setSign b lit
        | b == isPositive lit = lit
        | otherwise           = neg lit
    unsign :: l -> Variable l
    -- | Gives a sign to a variable. 'True' stands for +.
    lit :: Bool -> Variable l -> l
    createHelperPool :: Proxy l -> Variable l -> [Variable (HelperLiteral l)]
    unsafeReadAllocation :: Proxy l -> Allocation l b -> Variable l -> b
    readAllocation :: Proxy l -> Allocation l b -> Variable l -> Maybe b
    assocs :: Proxy l -> Allocation l b -> [(Variable l,b)]
    makeVarCache :: Proxy l -> GeneralVarCache (Variable l)
    arrayIntoAllocation :: (Ix e, Integral e) => Proxy l -> GeneralVarCache (Variable l) -> Data.Array.Array e b -> Allocation l b

integralToLit :: (Literal l, VarCache c (Variable l), Integral e) => c (Variable l) -> e -> Maybe l
integralToLit cache i = lit (i > 0) <$> integralToVar cache (abs i)

litToIntegral :: (Literal l, VarCache c (Variable l), Integral e) => c (Variable l) -> l -> Maybe e
litToIntegral cache l 
    | isPositive l = i
    | otherwise    = negate <$> i
    where i = varToIntegral cache (unsign l)

litSatisfied :: forall l b . (Literal l, BoolLike b) => Allocation l b -> l -> LBool
litSatisfied allo l
    | Nothing <- a= LUndef
    | b == ltrue  = boolToBoolLike $ isPositive l
    | b == lfalse = boolToBoolLike $ not $ isPositive l
    | otherwise   = LUndef
    where
        a = readAllocation (Proxy :: Proxy l) allo (unsign l)
        Just b = a

instance Ord a => Literal (Lit a) where
    type Variable (Lit a) = a
    type HelperLiteral (Lit a) = Lit (Either Int a)
    type Allocation (Lit a) = Data.Map.Map a
    neg (Pos x) = Neg x
    neg (Neg x) = Pos x
    isPositive (Pos _) = True
    isPositive (Neg _) = False
    unsign (Pos x) = x
    unsign (Neg x) = x
    lit True  = Pos
    lit False = Neg
    createHelperPool _ _ = map Left [0..]
    unsafeReadAllocation _ = (Data.Map.!)
    readAllocation _ = (Data.Map.!?)
    assocs _ = Data.Map.assocs
    makeVarCache _ = GeneralVarCache $ VarCacheOrd []
    arrayIntoAllocation _ = mapArrayOnMap

instance (Enum a, Num a, Ord a, Ix a, Integral a) => Literal (ByNumber a) where
    type Variable (ByNumber a) = ByNumber a
    type HelperLiteral (ByNumber a) = ByNumber a
    type Allocation (ByNumber a) = Data.Array.Array a
    neg = fmap negate
    isPositive = (> ByNumber 0)
    setSign True  = fmap abs
    setSign False = neg . fmap abs
    unsign = setSign True
    lit b x
        | isPositive x = setSign b x
        | otherwise = error "Not a valid variable name."
    createHelperPool _ m = [succ m..]
    unsafeReadAllocation _ a (ByNumber i) = a Data.Array.! i
    readAllocation p a (ByNumber i)
        | inRange (Data.Array.bounds a) i = Just $ unsafeReadAllocation p a (ByNumber i)
        | otherwise = Nothing
    assocs _ = map (first ByNumber) . Data.Array.assocs
    makeVarCache _ = GeneralVarCache VarCacheIntegral
    arrayIntoAllocation _ cache arr = Data.Array.ixmap b fromIntegral arr
        where b = bimap fromIntegral fromIntegral $ Data.Array.bounds arr

isNegative :: (Literal l) => l -> Bool
isNegative = not . isPositive

newtype ByNumber a = ByNumber a
    deriving (Eq, Ord, Functor, Enum, Ix)
    deriving newtype (Show, Read, Real, Num, Integral)

-- | A literal is a positive or negative atom.
data Lit a = Neg a | Pos a
    deriving (Eq, Ord, Functor, Foldable, Traversable)

instance Applicative Lit where
    pure = Pos
    (<*>) = ap

instance Monad Lit where
    Pos x >>= f = f x
    Neg x >>= f = case f x of
        Pos y -> Neg y
        Neg y -> Pos y

instance Show a => Show (Lit a) where
    show (Pos a) = '+' : show a
    show (Neg a) = '-' : show a

instance Read a => Read (Lit a) where
    readsPrec prec ('+':rest) = first Pos <$> readsPrec prec rest
    readsPrec prec ('-':rest) = first Neg <$> readsPrec prec rest
    readsPrec prec _          = []

-- | Create an Empty Literal with given sign. 
fromBool :: Bool -> Lit ()
fromBool = (`lit` ())


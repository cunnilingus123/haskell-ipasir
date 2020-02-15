{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module SAT.IPASIR.Literals
    ( Lit (..)
    , LBool (..)
    , lit
    , fromBool
    , neg
    , isPositive
    , extract
    , flatLit
    , enumToLBool
    ) where

import Data.String (IsString(..))
import Data.Bits (xor)

import Control.Monad (Monad(..), ap)
import Control.Comonad (Comonad(..))

-- | A solution for a single variable.
-- @Just a@ indicates that the variable is @a@ in the solution
-- @Nothing@ indicates that the variable is not important for the solution.
-- both @True@ and @False@ are valid assignments.
-- 
-- Working with this representation may be cumbersome. If you do not want to
-- deal with unimportant variables pass your solutions through @expandSolution@.
data LBool = LFalse | LUndef | LTrue deriving (Eq,Ord,Bounded)

instance Show LBool where
    show LTrue  = "1"
    show LFalse = "0"
    show LUndef = "?"

instance Enum LBool where
    fromEnum LTrue  =  1
    fromEnum LFalse = -1
    fromEnum LUndef = 0
    toEnum i
        | i == 0    = LUndef
        | i <  0    = LFalse
        | otherwise = LTrue

enumToLBool :: (Ord a, Num a) => a -> LBool
enumToLBool i = case compare i 0 of
    GT -> LTrue
    EQ -> LUndef
    _  -> LFalse

instance Read LBool where


-- | A literal is a positive or negative atom.
data Lit a
    = Pos a
    | Neg a
    deriving (Eq, Functor, Foldable, Traversable)

-- | We order literals first by variable, then by sign, so that dual
-- literals are neighbors in the ordering.
instance (Ord a) => Ord (Lit a) where
    compare x y = shim x `compare` shim y
        where
            shim l = (extract l, isPositive l)

instance Applicative Lit where
    pure = Pos
    (<*>) = ap

instance Monad Lit where
    l >>= f = s `lit` extract l'
        where
            s = isPositive l `xor` isPositive l'
            l' = f $ extract l

instance Comonad Lit where
    extract (Pos a) = a
    extract (Neg a) = a

    duplicate (Pos a) = Pos $ Pos a
    duplicate (Neg a) = Neg $ Pos a

instance Show a => Show (Lit a) where
    show (Pos a) = '+' : show a
    show (Neg a) = '-' : show a

instance IsString a => IsString (Lit a) where
    fromString = return . fromString

-- | Create a Literal with given sign. 
lit :: Bool -> a -> Lit a
lit True  = Pos
lit False = Neg

-- | Create an Empty Literal with given sign. 
fromBool :: Bool -> Lit ()
fromBool = (`lit` ())

-- | Negate a literal.
neg :: Lit a -> Lit a
neg (Pos a) = Neg a
neg (Neg a) = Pos a

-- | Get the sign of a 'Literal' ('True' for positive).
isPositive :: Lit a -> Bool
isPositive (Pos _) = True
isPositive (Neg _) = False

flatLit :: Num e => Lit e -> e
flatLit (Pos i) = i
flatLit (Neg i) = -i

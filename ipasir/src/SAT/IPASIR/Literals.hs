{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module SAT.IPASIR.Literals
    ( Lit (..)
    , lit
    , fromBool
    , neg
    , isPositive
    , extract
    , flatLit
    ) where

import Data.String (IsString(..))
import Data.Bits (xor)
import Data.Bifunctor (first)

import Control.Monad (Monad(..), ap)
import Control.Comonad (Comonad(..))



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
            s = isPositive l == isPositive l'
            l' = f $ extract l

instance Comonad Lit where
    extract (Pos a) = a
    extract (Neg a) = a

    duplicate (Pos a) = Pos $ Pos a
    duplicate (Neg a) = Neg $ Pos a

instance Show a => Show (Lit a) where
    show (Pos a) = '+' : show a
    show (Neg a) = '-' : show a

instance Read a => Read (Lit a) where
    readsPrec prec ('+':rest) = first Pos <$> readsPrec prec rest
    readsPrec prec ('-':rest) = first Neg <$> readsPrec prec rest
    readsPrec prec _          = []

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

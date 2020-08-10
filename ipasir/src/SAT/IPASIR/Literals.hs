{-# LANGUAGE TypeFamilies #-}
-- {-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module SAT.IPASIR.Literals
    ( Literal (..)
    , Lit (..)
    , fromBool
    , flatLit
    ) where

import Data.String (IsString(..))
import Data.Bits (xor)
import Data.Bifunctor (first)
import Foreign.C.Types (CInt(..),CUInt(..))
import Unsafe.Coerce (unsafeCoerce)
import Data.Proxy (Proxy)

import Control.Monad (Monad(..), ap)

-- | > isPositive . neg = not . isPositive
--   > isPositive (setSign b lit) = b
class Literal l where
    type Variable l
    type HelperVariable l

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
    lit :: Bool -> Variable l -> l
    createHelperPool :: Proxy l -> Variable l -> [HelperVariable l]

instance Literal (Lit a) where
    type Variable (Lit a) = a
    type HelperVariable (Lit a) = Either Int a
    neg (Pos x) = Neg x
    neg (Neg x) = Pos x
    isPositive (Pos _) = True
    isPositive (Neg _) = False
    unsign (Pos x) = x
    unsign (Neg x) = x
    lit True  = Pos
    lit False = Neg
    createHelperPool _ _ = map Left [0..]

{-
instance (Enum a) => Literal (ByNumber a) where
    type Variable (ByNumber a) = ByNumber a
    type HelperVariable (ByNumber a) = ByNumber a
    neg = fmap negate
    isPositive = (> ByNumber 0)
    setSign True  = fmap abs
    setSign False = neg . fmap abs
    unsign = setSign True
    lit b x
        | isPositive x = setSign b x
        | otherwise = error "Not a valid variable name."
    createHelperPool _ m = [succ m..]
-}
    

newtype ByNumber a = ByNumber a
    deriving (Eq, Ord, Show, Functor)

-- | A literal is a positive or negative atom.
data Lit a = Neg a | Pos a
    deriving (Eq, Ord, Functor, Foldable, Traversable)

instance Applicative Lit where
    pure = Pos
    (<*>) = ap

instance Monad Lit where
    l >>= f = s `lit` unsign l'
        where
            s = isPositive l == isPositive l'
            l' = f $ unsign l

instance Show a => Show (Lit a) where
    show (Pos a) = '+' : show a
    show (Neg a) = '-' : show a

instance Read a => Read (Lit a) where
    readsPrec prec ('+':rest) = first Pos <$> readsPrec prec rest
    readsPrec prec ('-':rest) = first Neg <$> readsPrec prec rest
    readsPrec prec _          = []

instance IsString a => IsString (Lit a) where
    fromString = return . fromString

-- | Create an Empty Literal with given sign. 
fromBool :: Bool -> Lit ()
fromBool = (`lit` ())

flatLit :: Num e => Lit e -> e
flatLit (Pos i) = i
flatLit (Neg i) = -i









{-
instance Literal Int Word where
    neg = negate
    isPositive = (>0)
    setSign True = abs
    setSign _    = neg . abs
    unsign = fromIntegral . abs
    lit b v 
        | posL <= 0 = error $ "The variable " ++ show v 
                                    ++ " has an invalid number. It is either zero or to high for being kept inside an Int."
        | b = posL
        | otherwise = negate posL
        where
            posL = unsafeCoerce v

instance Literal CInt CUInt where
    neg = negate
    isPositive = (>0)
    setSign True = abs
    setSign _    = neg . abs
    unsign = fromIntegral . abs
    lit b v 
        | posL <= 0 = error $ "The variable " ++ show v 
                                    ++ " has an invalid number. It is either zero or to high for being kept inside an CInt."
        | b = posL
        | otherwise = negate posL
        where
            posL = unsafeCoerce v
-}
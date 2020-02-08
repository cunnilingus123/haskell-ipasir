module SAT.PseudoBoolean.WeightedLit
    ( WLit(..)
    , WeightedLit(..)
    , ($-$)
    , weightedLit
    ) where

import SAT.PseudoBoolean.Config (coerceEnum)

import Foreign.Ptr      (Ptr, castPtr)
import Foreign.Storable (Storable(..))
import Foreign.C.Types  (CInt(..), CLong(..))

-- | This typeclass summarizes 'WeightedLit' and 'Int'. An 'Int' counts as a
--   literal with weight 1.
class WLit a where
    weightit :: a -> WeightedLit

instance WLit WeightedLit where
    weightit = id

instance WLit Int where
    weightit = ($-$ 1)

-- | A single summand in a pseudo boolean constraint.
data WeightedLit = WeightedLit 
    { literal :: CInt
    , weight :: CLong
    } deriving (Show, Read, Eq, Ord)

-- | Better version of 'weightedLit' due to the fact that this
--   operator looks like a dumbbell.
($-$) :: (Enum l, Integral w) => l -> w -> WeightedLit
($-$) = weightedLit

-- | Creates a 'WeightedLit' but is more general than the constructor 
--   so you dont have to
--   use 'Foreign.C.Types.CInt' nor 'Foreign.C.Types.CLong'.
weightedLit :: (Enum l, Integral w) => l -> w -> WeightedLit
weightedLit l w = WeightedLit (coerceEnum l) (fromInteger $ toInteger w)

instance Storable WeightedLit where
    sizeOf _ = sizeOf (undefined :: Ptr WeightedLit)
    alignment = sizeOf
    peek ptr = undefined
    poke ptr wl = do
        wlPtr <- new_WeightedLit (literal wl) (weight wl)
        poke (castPtr ptr) wlPtr

foreign import ccall unsafe "pblib_c.h new_WeightedLit" new_WeightedLit :: CInt -> CLong -> IO (Ptr WeightedLit)

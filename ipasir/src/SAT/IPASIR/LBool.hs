module SAT.IPASIR.LBool
    ( LBool (..)
    , BoolLike (..)
    , enumToLBool
    ) where

import Data.Bits (xor)

-- | A solution for a single variable.
-- @Just a@ indicates that the variable is @a@ in the solution
-- @Nothing@ indicates that the variable is not important for the solution.
-- both @True@ and @False@ are valid assignments.
-- 
-- Working with this representation may be cumbersome. If you do not want to
-- deal with unimportant variables pass your solutions through @expandSolution@.
data LBool = LFalse | LUndef | LTrue deriving (Eq,Ord,Bounded)

-- | Summarizes @Bool@ and @LBool@.
class Eq b => BoolLike b where
    ltrue  :: b
    lfalse :: b
    lfalse = lnot ltrue
    -- | Negation
    lnot   :: b -> b
    -- | Logical and.
    (&&*) :: b -> b -> b
    -- | Logical or.
    (||*) :: b -> b -> b
    -- | Logical exclusive or.
    (++*) :: b -> b -> b
    -- | Logical implication.
    (->*)  :: b -> b -> b
    x ->* y  = lnot x ||* y
    -- | Logical equivalence.
    (<->*) :: b -> b -> b
    x <->* y = lnot $ x ++* y

    land   :: Foldable t => t b -> b
    land = foldl (&&*) ltrue
    lor    :: Foldable t => t b -> b
    lor  = foldl (||*) lfalse
    lxor   :: Foldable t => t b -> b
    lxor = foldl (++*) lfalse
    boolToBoolLike :: Bool -> b
    boolToBoolLike b = if b then ltrue else lfalse

instance BoolLike LBool where
    ltrue  = LTrue
    lfalse = LFalse

    lnot LTrue  = LFalse
    lnot LFalse = LTrue
    lnot LUndef = LUndef

    LFalse &&* _      = LFalse
    _      &&* LFalse = LFalse
    LTrue  &&* LTrue  = LTrue
    _      &&* _      = LUndef

    LTrue  ||* _      = LTrue
    _      ||* LTrue  = LTrue
    LFalse ||* LFalse = LFalse
    _      ||* _      = LUndef

    LUndef ++* _      = LUndef
    _      ++* LUndef = LUndef
    LFalse ++* LFalse = LFalse
    LTrue  ++* LTrue  = LFalse
    _      ++* _      = LTrue


instance BoolLike Bool where
    ltrue  = True
    lfalse = False
    lnot   = not
    (&&*)  = (&&)
    (||*)  = (||)
    (++*)  = (/=)
    (<->*) = (==)
    land   = and
    lor    = or
    boolToBoolLike = id

enumToLBool :: (Ord a, Num a) => a -> LBool
enumToLBool i = case compare i 0 of
    GT -> LTrue
    EQ -> LUndef
    _  -> LFalse

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

instance Read LBool where
    readsPrec prec ('1':str) = [(LTrue ,str)]
    readsPrec prec ('0':str) = [(LFalse,str)]
    readsPrec prec ( _ :str) = [(LUndef,str)]

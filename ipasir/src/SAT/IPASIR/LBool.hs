module SAT.IPASIR.LBool
    ( LBool (..)
    , lnot
    , land
    , lor
    , lxor
    , enumToLBool
    ) where

-- | A solution for a single variable.
-- @Just a@ indicates that the variable is @a@ in the solution
-- @Nothing@ indicates that the variable is not important for the solution.
-- both @True@ and @False@ are valid assignments.
-- 
-- Working with this representation may be cumbersome. If you do not want to
-- deal with unimportant variables pass your solutions through @expandSolution@.
data LBool = LFalse | LUndef | LTrue deriving (Eq,Ord,Bounded)

enumToLBool :: (Ord a, Num a) => a -> LBool
enumToLBool i = case compare i 0 of
    GT -> LTrue
    EQ -> LUndef
    _  -> LFalse

-- | Negates an 'lBool'.
lnot :: LBool -> LBool
lnot LTrue  = LFalse
lnot LFalse = LTrue
lnot LUndef = LUndef

land :: LBool -> LBool -> LBool
land LFalse _ = LFalse
land _ LFalse = LFalse
land LTrue LTrue = LTrue
land _ _ = LUndef

lor :: LBool -> LBool -> LBool
lor LTrue _ = LTrue
lor _ LTrue = LTrue
lor LFalse LFalse = LFalse
lor _ _ = LUndef

lxor :: LBool -> LBool -> LBool
lxor LUndef _ = LUndef
lxor _ LUndef = LUndef
lxor LFalse LFalse = LFalse
lxor LTrue  LTrue  = LFalse
lxor _  _          = LTrue

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

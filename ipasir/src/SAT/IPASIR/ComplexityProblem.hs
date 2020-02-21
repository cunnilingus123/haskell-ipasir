{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

module SAT.IPASIR.ComplexityProblem where

import Data.Proxy (Proxy(..))
import Data.Bifunctor (Bifunctor(..))
import Data.Array (Array, assocs, bounds, ixmap, (!))
import Data.Ix (Ix(..))
import Foreign.C.Types (CInt)

import Control.Monad ((<=<))

import SAT.IPASIR.Literals (LBool(..))

class ComplexityProblem cp where
    type Solution cp

class (ComplexityProblem cp) => AssumingProblem cp where
    type Assumption cp
    type Conflict cp

-- | Every 'Solver' returns either a 'Solution' (also called model or proof).
type Result cp = Maybe (Solution cp)

-- | (👉) represents a new solver (or reduction) using a 'Reduction'.
--   If the left side 'r' is a 'Reduction' and the right side 's' is a 
-- 'SAT.IPASIR.Solver.Solver', an 'SAT.IPASIR.Solver.IncrementalSolver' or
-- 'Reduction', then 'r 👉 s' fullfills the same constraints like 's'.
data r 👉 s = r :👉 s
infixl 3 👉
infixl 3 :👉

instance Bifunctor (👉) where
    bimap f g (r :👉 s) = f r :👉 g s

-- | A subclass of 'ComplexityProblem' which can make encodings
--   for a certain solution or makes an encoding, which refuses
--   a certain solution.
class (ComplexityProblem cp) => Solutiontransform cp where
    -- | Returns an encoding which will have a certain (unique) solution.
    solutionToEncoding    :: Solution cp -> cp
    -- | Returns an encoding for which every solution except the given 
    --   one is a valid.
    negSolutionToEncoding :: Solution cp -> cp

-- | A reduction parses one 'ComplexityProblem' into another.
class (ComplexityProblem (CPFrom r), ComplexityProblem (CPTo r)) => Reduction r where

    type CPFrom r
    type CPTo   r
    -- | Sets up a new reduction layer. A reduction layer is only needed
    --   if you have to memorize stuff after a reduction. For example variable
    --   names. In most cases this one will be 'Data.Proxy.Proxy'.
    newReduction  :: r
    -- | Parses an 'Encoding'. Notice, that the returned new reduction needs 
    --   to remember some renaming details like variablenames to parse a 
    --   'Solution' (or 'Conflict' or 'Assumption') back.
    parseEncoding :: r -> CPFrom r -> (CPTo r, r)
    -- | Parses a 'Solution' of a 'ComplexityProblem' back.
    parseSolution :: r -> Solution (CPTo r) -> Solution (CPFrom r)

class (AssumingProblem (CPFrom r), AssumingProblem (CPTo r), Reduction r) 
      => AReduction r where
    -- | Parses a 'Conflict' of a 'ComplexityProblem' back.
    parseConflict :: r -> Conflict (CPTo r) -> Conflict (CPFrom r)
    -- | Parses the 'Assumption' into an equivalent sequence of other assumptions.
    parseAssumption :: r -> Assumption (CPFrom r) -> [Assumption (CPTo r)]

instance (Reduction r1, Reduction r2, CPFrom r2 ~ CPTo r1) => Reduction (r2 👉 r1) where
    type CPFrom (r2 👉 r1) = CPFrom r1
    type CPTo   (r2 👉 r1) = CPTo   r2
    newReduction  = newReduction :👉 newReduction
    parseEncoding (r2 :👉 r1) e = (e'', r'' :👉 r')
        where
            (e' ,r' ) = parseEncoding r1 e
            (e'',r'') = parseEncoding r2 e'
    parseSolution   (r2 :👉 r1) = parseSolution   r1  .  parseSolution   r2

instance (AReduction r1, AReduction r2, CPFrom r2 ~ CPTo r1) => AReduction (r2 👉 r1) where
    parseConflict   (r2 :👉 r1) = parseConflict   r1  .  parseConflict   r2
    parseAssumption (r2 :👉 r1) = parseAssumption r2 <=< parseAssumption r1

-- | This reduction changes the Boolean type from 'Bool' to 'LBool'.
data RedBoolLBool (cp :: * -> *) = RedBoolLBool

-- | This reduction changes the Boolean type from 'LBool' to 'Bool'.
--   In case of an 'LUndef' goes to True.
data RedLBoolTrue (cp :: * -> *) = RedLBoolTrue

-- | This reduction changes the Boolean type from 'LBool' to 'Bool'.
--   In case of an 'LUndef' goes to False.
data RedLBoolFalse (cp :: * -> *) = RedLBoolFalse

-- | This reduction changes the Enum type from 'e' to 'i' by using 'toEnum . fromEnum' 
--   in case the complexity problem uses Enums to express the variables.
data RedEnum (cp :: * -> * -> *) e i b = RedEnum

newtype BoolLBoolDerive  (cp :: * -> * -> *) x = BoolLBoolDerive  (RedBoolLBool (cp x))
newtype LBoolTrueDerive  (cp :: * -> * -> *) x = LBoolTrueDerive  (RedLBoolTrue (cp x))
newtype LBoolFalseDerive (cp :: * -> * -> *) x = LBoolFalseDerive (RedLBoolFalse (cp x))
newtype EnumDerive (cp :: * -> * -> *) e i b   = EnumDerive (RedEnum cp e i b)

instance ( ComplexityProblem (cp x LBool)
         , ComplexityProblem (cp x Bool)
         , Bifunctor cp
         , f LBool ~ Solution (cp x LBool)
         , f  Bool ~ Solution (cp x  Bool)
         , Functor f
         ) => Reduction (BoolLBoolDerive cp x) where
    type CPFrom (BoolLBoolDerive cp x) = cp x LBool
    type CPTo   (BoolLBoolDerive cp x) = cp x  Bool
    newReduction    = BoolLBoolDerive RedBoolLBool
    parseEncoding _ = (, BoolLBoolDerive RedBoolLBool) . second undefined
    parseSolution _ = fmap boolToLBool
        where
            boolToLBool :: Bool -> LBool
            boolToLBool True = LTrue
            boolToLBool _    = LFalse

instance ( Reduction (BoolLBoolDerive cp x)
         , AssumingProblem (cp x Bool)
         , AssumingProblem (cp x LBool)
         , Assumption (cp x Bool) ~ Assumption (cp x LBool)
         , Conflict   (cp x Bool) ~ Conflict   (cp x LBool)
         ) => AReduction (BoolLBoolDerive cp x) where
    parseConflict   _ = id
    parseAssumption _ = pure


instance ( ComplexityProblem (cp x LBool)
         , ComplexityProblem (cp x Bool)
         , Bifunctor cp
         , f LBool ~ Solution (cp x LBool)
         , f  Bool ~ Solution (cp x  Bool)
         , Functor f
         ) => Reduction (LBoolTrueDerive cp x) where
    type CPFrom (LBoolTrueDerive cp x) = cp x  Bool
    type CPTo   (LBoolTrueDerive cp x) = cp x LBool
    newReduction    = LBoolTrueDerive RedLBoolTrue
    parseEncoding _ = (, LBoolTrueDerive RedLBoolTrue) . second undefined
    parseSolution _ = fmap (/=LFalse)

instance ( Reduction (LBoolTrueDerive cp x)
         , AssumingProblem (cp x Bool)
         , AssumingProblem (cp x LBool)
         , Assumption (cp x Bool) ~ Assumption (cp x LBool)
         , Conflict   (cp x Bool) ~ Conflict   (cp x LBool)
         ) => AReduction (LBoolTrueDerive cp x) where
    parseConflict   _ = id
    parseAssumption _ = pure

instance ( ComplexityProblem (cp x LBool)
         , ComplexityProblem (cp x Bool)
         , Bifunctor cp
         , f LBool ~ Solution (cp x LBool)
         , f  Bool ~ Solution (cp x  Bool)
         , Functor f
         ) => Reduction (LBoolFalseDerive cp x) where
    type CPFrom (LBoolFalseDerive cp x) = cp x  Bool
    type CPTo   (LBoolFalseDerive cp x) = cp x LBool
    newReduction    = LBoolFalseDerive RedLBoolFalse
    parseEncoding _ = (, LBoolFalseDerive RedLBoolFalse) . second undefined
    parseSolution _ = fmap (==LTrue)

instance ( Reduction (LBoolFalseDerive cp x)
         , AssumingProblem (cp x Bool)
         , AssumingProblem (cp x LBool)
         , Assumption (cp x Bool) ~ Assumption (cp x LBool)
         , Conflict   (cp x Bool) ~ Conflict   (cp x LBool)
         ) => AReduction (LBoolFalseDerive cp x) where
    parseConflict   _ = id
    parseAssumption _ = pure

instance ( ComplexityProblem (cp e b)
         , ComplexityProblem (cp i b)
         , Bifunctor cp
         , Enum e
         , Ix e 
         , Enum i
         , Ix i
         , Array e b ~ Solution (cp e b)
         , Array i b ~ Solution (cp i b)
         ) => Reduction (EnumDerive cp e i b) where
    type CPFrom (EnumDerive cp e i b) = cp e b
    type CPTo   (EnumDerive cp e i b) = cp i b
    newReduction    = EnumDerive RedEnum
    parseEncoding _ = (, EnumDerive RedEnum) . first (toEnum . fromEnum) 
    parseSolution _ = mapIndex parseEnum
        where
            parseEnum :: (Enum a, Enum b) => a -> b
            parseEnum = toEnum . fromEnum
            mapIndex :: (Ix e, Enum e, Ix i, Enum i) => (e -> i) -> Array i a -> Array e a
            mapIndex f arr = ixmap (bimap parseEnum parseEnum (bounds arr)) f arr


instance ( AssumingProblem (cp e b)
         , AssumingProblem (cp i b)
         , Bifunctor cp
         , Enum e
         , Ix e 
         , Enum i
         , Ix i
         , Array e b ~ Solution (cp e b)
         , Array i b ~ Solution (cp i b)
         , f e ~ Conflict (cp e b)
         , f i ~ Conflict (cp i b)
         , Functor f
         , e ~ Assumption (cp e b)
         , i ~ Assumption (cp i b)
         ) => AReduction (EnumDerive cp e i b) where
    parseConflict   _ = fmap (toEnum . fromEnum) 
    parseAssumption _ = pure . toEnum . fromEnum

instance Ix CInt where
    range (from, to) = [from..to]
    index (from, to) i
      | inRange (from, to) i = fromEnum $ i - from
      | otherwise            = error $ "Index out of bounds Exception. Index:" 
                                        ++ show i ++ " Bounds: " ++ show (from,to)
    inRange (from, to) i = i >= from && i <= to
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveFunctor #-}

module SAT.PseudoBoolean.CardinalityMonad where

import Control.Monad (ap)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Lazy (StateT, runStateT, get)

import Foreign.ForeignPtr (ForeignPtr, withForeignPtr, newForeignPtr)
import Foreign.Ptr (Ptr)

import Data.Proxy      (Proxy(..))
import Data.Reflection (Reifies(..))

import SAT.PseudoBoolean.Config      (Config, coerceEnum)
import SAT.PseudoBoolean.WeightedLit (WeightedLit, WLit(weightit))
import SAT.PseudoBoolean.C
    ( CEncoder
    , Comp(..)
    , cencoder
    , c_encodeNewGeq
    , c_encodeNewLeq
    , c_getClauses
    , free_C_Clauses
    , c_addConditional
    , c_clearConditional
    , c_clearDB
    , CVector(toList)
    , peek
    )

-- | A state-monad, which knows in the type system if it is possible to change the lower bound (incremental)
--   or the upper bound. 
newtype CardinalityMonad (lb :: Bool) (ub :: Bool) a = CardinalityMonad {st :: StateT (ForeignPtr CEncoder) IO a}
    deriving (Functor)

instance Monad (CardinalityMonad lb ub) where
    m >>= f = CardinalityMonad $ st m >>= st . f
instance Applicative (CardinalityMonad lb ub) where
    (<*>) = ap
    pure  = CardinalityMonad . pure 

instance Reifies True  Bool where
    reflect _ = True
instance Reifies False Bool where
    reflect _ = False

class (Reifies lb Bool, Reifies ub Bool) => BoundsOK (lb :: Bool) (ub :: Bool) t | lb ub -> t where
    toBounds :: Proxy lb -> Proxy ub -> t -> (Int, Int)
instance BoundsOK True True (Int,Int) where
    toBounds _ _ = id
instance BoundsOK True False Int where
    toBounds _ _ = (,0) -- The upper bound will be ignores in pblib_c.cpp
instance BoundsOK False True Int where
    toBounds _ _ = (0,) -- The lower bound will be ignores in pblib_c.cpp

toComp :: forall lb ub t a. BoundsOK lb ub t => CardinalityMonad lb ub a -> Comp
toComp _ = case (reflect (Proxy :: Proxy lb), reflect (Proxy :: Proxy ub)) of
    (True, True)  -> CBoth
    (True, False) -> CGeq
    (False, True) -> CLeq
    _             -> error "The Type CardinalityMonad False False a should not be possible."

evalEncoder :: forall lb ub t a l. (BoundsOK lb ub t, WLit l)
            => Config
            -> [l]
            -> t
            -> Int
            -> CardinalityMonad lb ub a
            -> IO a
evalEncoder config lits bounds firstFree body = fst <$> runEncoder config lits bounds firstFree body

runEncoder  :: forall lb ub t a l. (BoundsOK lb ub t, WLit l)
            => Config
            -> [l]
            -> t
            -> Int
            -> CardinalityMonad lb ub a
            -> IO (a, ForeignPtr CEncoder)
runEncoder config lits bounds firstFree body = do
    let comp = toComp body
    let (lower, upper) = toBounds (Proxy :: Proxy lb) (Proxy :: Proxy ub) bounds
    let lits' = map weightit lits
    e <- cencoder config lits' comp lower upper firstFree
    runStateT (st body) e

withEncoder :: (Ptr CEncoder -> IO a) -> CardinalityMonad lb ub a
withEncoder body = CardinalityMonad $ do
    encoder <- get
    lift $ withForeignPtr encoder body

-- | Same as 'encodeNewLeq' but for the lower bound.
encodeNewGeq :: Int -> CardinalityMonad True a ()
encodeNewGeq bound = withEncoder (`c_encodeNewGeq` coerceEnum bound)

-- | Sets a new upper bound. The return value is a logic formula in
--   conditional normal, which garantees that.
encodeNewLeq :: Int -> CardinalityMonad a True ()
encodeNewLeq bound = withEncoder (`c_encodeNewLeq` coerceEnum bound)

-- | See also 'bothLimited', 'belowLimited' and 'aboveLimited'.
getClauses :: CardinalityMonad a b [[Int]]
getClauses = withEncoder $ \encoder -> do
    clausesPtr <- newForeignPtr free_C_Clauses =<< c_getClauses encoder
    rawClauses <- withForeignPtr clausesPtr peek
    return $ map (map fromEnum . toList) $ toList rawClauses

-- | Same as 'getClauses' but concrete type.
bothLimited  :: CardinalityMonad True True  [[Int]]
-- | Same as 'getClauses' but concrete type.
belowLimited :: CardinalityMonad True False [[Int]]
-- | Same as 'getClauses' but concrete type.
aboveLimited :: CardinalityMonad False True [[Int]]
bothLimited  = getClauses
belowLimited = getClauses
aboveLimited = getClauses

addConditional :: Int -> CardinalityMonad a b ()
addConditional i = withEncoder (`c_addConditional` coerceEnum i)

clearConditionals :: CardinalityMonad a b ()
clearConditionals = withEncoder c_clearConditional 

clearDB :: CardinalityMonad a b ()
clearDB = withEncoder c_clearDB

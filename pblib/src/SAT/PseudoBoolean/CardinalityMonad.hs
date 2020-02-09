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
  {-   ( CEncoder
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
  -}
import Foreign.Storable (Storable(..))

-- | A state-monad, which knows in the type system if it is possible to change the lower bound (incremental)
--   or the upper bound. 
newtype CardinalityMonad a = CardinalityMonad {st :: StateT (ForeignPtr CEncoder) IO a}
    deriving (Functor)
instance Monad CardinalityMonad where
    m >>= f = CardinalityMonad $ st m >>= st . f
instance Applicative CardinalityMonad where
    (<*>) = ap
    pure  = CardinalityMonad . pure 

newtype CardinalityConstraint (lb :: Bool) (ub :: Bool) = CardinalityConstraint (Ptr CConstraint)

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

toComp :: forall lb ub t. BoundsOK lb ub t => CardinalityConstraint lb ub -> Comp
toComp _ = case (reflect (Proxy :: Proxy lb), reflect (Proxy :: Proxy ub)) of
    (True, True)  -> CBoth
    (True, False) -> CGeq
    (False, True) -> CLeq
    _             -> error "The Type CardinalityMonad False False a should not be possible."

evalEncoder :: Config
            -> Int
            -> CardinalityMonad a
            -> IO a
evalEncoder config firstFree body = fst <$> runEncoder config firstFree body

runEncoder  :: Config
            -> Int
            -> CardinalityMonad a
            -> IO (a, ForeignPtr CEncoder)
runEncoder config firstFree body = runStateT (st body) =<< cencoder config firstFree

withEncoder :: (Ptr CEncoder -> IO a) -> CardinalityMonad a
withEncoder body = CardinalityMonad $ do
    encoder <- get
    lift $ withForeignPtr encoder body

encodeConstraint :: forall lb ub t l. (BoundsOK lb ub t, WLit l)
                 => [l]
                 -> t
                 -> CardinalityMonad (CardinalityConstraint lb ub)
encodeConstraint lits border = do
    let lits  = map weightit lits
        (l,u) = toBounds (Proxy :: Proxy lb) (Proxy :: Proxy ub) border
        comp  = toComp (undefined :: CardinalityConstraint lb ub)
    withEncoder $ \enc -> CardinalityConstraint <$> cconstraint enc lits comp l u

-- | Same as 'encodeNewLeq' but for the lower bound.
encodeNewGeq :: CardinalityConstraint True a -> Int -> CardinalityMonad ()
encodeNewGeq (CardinalityConstraint cc) bound 
    = withEncoder $ \enc -> c_encodeNewGeq enc cc (coerceEnum bound)

-- | Sets a new upper bound. The return value is a logic formula in
--   conditional normal, which garantees that.
encodeNewLeq :: CardinalityConstraint a True -> Int -> CardinalityMonad ()
encodeNewLeq (CardinalityConstraint cc) bound 
    = withEncoder $ \enc -> c_encodeNewLeq enc cc (coerceEnum bound)

getClauses :: CardinalityMonad [[Int]]
getClauses = withEncoder $ \encoder -> do
    clausesPtr <- newForeignPtr free_C_Clauses =<< c_getClauses encoder
    rawClauses <- withForeignPtr clausesPtr peek
    return $ map (map fromEnum . toList) $ toList rawClauses

-- | Same as 'encodeConstraint' but concrete typed.
encodeBoth :: WLit l => [l] -> (Int,Int) -> CardinalityMonad (CardinalityConstraint True True)
-- | Same as 'encodeConstraint' but concrete typed.
encodeGeq  :: WLit l => [l] ->  Int      -> CardinalityMonad (CardinalityConstraint True False)
-- | Same as 'encodeConstraint' but concrete typed.
encodeLeq  :: WLit l => [l] ->  Int      -> CardinalityMonad (CardinalityConstraint False True)
encodeBoth = encodeConstraint
encodeGeq  = encodeConstraint
encodeLeq  = encodeConstraint

addConditional :: CardinalityConstraint a b -> Int -> CardinalityMonad ()
addConditional (CardinalityConstraint cc) i
    = withEncoder $ \enc -> c_addConditional enc cc (coerceEnum i)

clearConditionals :: CardinalityConstraint a b -> CardinalityMonad ()
clearConditionals (CardinalityConstraint cc)
    = withEncoder $ \enc -> c_clearConditional enc cc 

clearDB :: CardinalityMonad ()
clearDB = withEncoder c_clearDB

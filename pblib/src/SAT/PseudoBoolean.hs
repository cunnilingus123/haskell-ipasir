module SAT.PseudoBoolean
    ( weightedLit
    , ($-$)
    , WeightedLit(..)
    , defaultConfig
    , Config(..)
    , BimanderMIs(..)
    , AMO_ENCODER (..)
    , AMK_ENCODER (..)
    ,  PB_ENCODER (..)
    , Comp(..)
    , Encoder
    , runEncoder
    , evalEncoder
    , encodeNewGeq
    , encodeNewLeq
    , getClauses
    ) where

import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Lazy
import System.IO.Unsafe

import Foreign.ForeignPtr

import Data.Word
import Data.Int

import SAT.PseudoBoolean.C
import SAT.PseudoBoolean.Config
import SAT.PseudoBoolean.C.Types.WeightedLit

type Encoder a = StateT (ForeignPtr C_Encoder) IO a

evalEncoder :: Config -> [WeightedLit] -> Comp -> Int -> Int -> Int -> Encoder b -> IO b
evalEncoder config lits comp lower upper firstFree body = fst <$> runEncoder config lits comp lower upper firstFree body

runEncoder  :: Config -> [WeightedLit] -> Comp -> Int -> Int -> Int -> Encoder b -> IO (b, ForeignPtr C_Encoder)
runEncoder config lits comp lower upper firstFree body = do 
    e <- cencoder config lits comp lower upper firstFree
    runStateT body e

withEncoder :: (ForeignPtr C_Encoder -> IO a)
                -> StateT (ForeignPtr C_Encoder) IO [[Int]]
withEncoder body = do
    encoder <- get
    lift $ body encoder
    lift $ cgetClauses encoder

encodeNewGeq :: Int64 -> Encoder [[Int]]
encodeNewGeq bound = withEncoder (`cencodeNewGeq` bound)

encodeNewLeq :: Int64 -> Encoder [[Int]]
encodeNewLeq bound = withEncoder (`cencodeNewLeq` bound)

getClauses :: Encoder [[Int]]
getClauses = withEncoder return

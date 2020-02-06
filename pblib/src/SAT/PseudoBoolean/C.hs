module SAT.PseudoBoolean.C
    ( cencoder
    , cencodeNewGeq
    , cencodeNewLeq
    , cgetClauses
    , Comp(..)
    , C_Encoder
    ) where

import Data.Maybe
import Data.Word
import Data.Int
import Data.Bits

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable
import Foreign.C.Types
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array

import GHC.Generics

import SAT.PseudoBoolean.C.Types.WeightedLit
import SAT.PseudoBoolean.C.Types.CVector
import SAT.PseudoBoolean.C.Bindings
import SAT.PseudoBoolean.Config

data Comp
    = CLeq
    | CGeq
    | CBoth
        deriving (Show, Eq, Enum, Ord)

cencoder :: Config -> [WeightedLit] -> Comp -> Int -> Int -> Int -> IO (ForeignPtr C_Encoder)
cencoder config lits comp lowerBound upperBound firstFreeLit = do
    ptr <- mallocArray (length lits) :: IO (Ptr WeightedLit)
    pokeArray (castPtr ptr) lits
    let size   = coerceEnum $ length lits
    let ccomp  = coerceEnum comp
    let clower = coerceEnum lowerBound
    let cupper = coerceEnum upperBound
    let cfirstFree = coerceEnum firstFreeLit
    rawEncoder <- toEncoder config ptr size ccomp clower cupper cfirstFree
    newForeignPtr free_C_Encoder rawEncoder


toEncoder :: Config -> Ptr WeightedLit -> CSize -> CInt -> CLong -> CLong -> CInt -> IO (Ptr C_Encoder)
toEncoder = new_C_Encoder <$> (coerceEnum <$> pb_encoder)
                          <*> (coerceEnum <$> amk_encoder)
                          <*> (coerceEnum <$> amo_encoder)
                          <*> (coerceEnum <$> bimander_m_is)
                          <*> (coerceEnum <$> bimander_m)
                          <*> (coerceEnum <$> k_product_minimum_lit_count_for_splitting)
                          <*> (coerceEnum <$> k_product_k)
                          <*> (coerceEnum <$> commander_encoding_k)
                          <*> (coerceEnum <$> max_clauses_per_constant)
                          <*> (coerceEnum <$> use_formula_cache)
                          <*> (coerceEnum <$> print_used_encodings)
                          <*> (coerceEnum <$> checkForDuplicateLiterals)
                          <*> (coerceEnum <$> use_gac_binary_merge)
                          <*> (coerceEnum <$> binary_merge_no_support_for_single_bits)
                          <*> (coerceEnum <$> use_recursive_bdd_test)
                          <*> (coerceEnum <$> use_real_robdds)
                          <*> (coerceEnum <$> use_watch_dog_encoding_in_binary_merger)
                          <*> (coerceEnum <$> justApproximate)
                          <*> (coerceEnum <$> approximateMaxValue)


cencodeNewGeq :: ForeignPtr C_Encoder -> Int64 -> IO ()
cencodeNewGeq encoderPtr bound = withForeignPtr encoderPtr doGeq
    where
        doGeq ptr = c_encodeNewGeq ptr $ coerceEnum bound

cencodeNewLeq :: ForeignPtr C_Encoder -> Int64 -> IO ()
cencodeNewLeq encoderPtr bound = withForeignPtr encoderPtr doLeq
    where
        doLeq ptr = c_encodeNewLeq ptr $ coerceEnum bound

cgetClauses :: ForeignPtr C_Encoder -> IO [[Int]]
cgetClauses encoder = do
    clausesPtr <- newForeignPtr free_C_Clauses =<< withForeignPtr encoder c_getClauses
    rawClauses <- withForeignPtr clausesPtr peek
    return $ map (map fromEnum . toList) $ toList rawClauses

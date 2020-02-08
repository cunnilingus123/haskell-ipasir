{-# LANGUAGE DeriveGeneric #-}

module SAT.PseudoBoolean.Config
    ( coerceEnum
    , AMO_ENCODER(..)
    , AMK_ENCODER(..)
    , PB_ENCODER(..)
    , BimanderMIs(..)
    , Config (..)
    , defaultConfig
    , justApproximate
    , approximateMaxValue
    ) where

import Data.Maybe (isJust, fromMaybe)

import GHC.Generics (Generic)

-- | Just 'toEnum . fromEnum'
coerceEnum :: (Enum a, Enum b) => a -> b
coerceEnum = toEnum . fromEnum

data AMO_ENCODER
    = AMO_BEST
    | AMO_NESTED
    | AMO_BDD
    | AMO_BIMANDER
    | AMO_COMMANDER
    | AMO_KPRODUCT
    | AMO_BINARY
    | AMO_PAIRWISE
    deriving (Eq, Ord, Enum, Bounded, Show, Read, Generic)

data AMK_ENCODER
    = AMK_BEST
    | AMK_BDD
    | AMK_CARD
    deriving (Eq, Ord, Enum, Bounded, Show, Read, Generic)

data PB_ENCODER
    = PB_BEST
    | PB_BDD
    | PB_SWC
    | PB_SORTINGNETWORKS
    | PB_ADDER
    | PB_BINARY_MERGE
    deriving (Eq, Ord, Enum, Bounded, Show, Read, Generic)

data BimanderMIs
    = Half
    | Sqrt
    | Fixed
    deriving (Eq, Ord, Enum, Bounded, Show, Read, Generic)

data Config = Config
    { pb_encoder  :: PB_ENCODER
    , amk_encoder :: AMK_ENCODER
    , amo_encoder  :: AMO_ENCODER
    , bimander_m_is :: BimanderMIs
    , bimander_m :: Int
    , k_product_minimum_lit_count_for_splitting :: Int
    , k_product_k :: Int
    , commander_encoding_k ::Int
    , max_clauses_per_constant ::Int
    , use_formula_cache :: Bool
    , print_used_encodings :: Bool
    , checkForDuplicateLiterals :: Bool
    , use_gac_binary_merge :: Bool
    , binary_merge_no_support_for_single_bits :: Bool
    , use_recursive_bdd_test :: Bool
    , use_real_robdds :: Bool
    , use_watch_dog_encoding_in_binary_merger :: Bool
    , approximate :: Maybe Int
    } deriving (Eq, Show, Read, Generic)

defaultConfig :: Config
defaultConfig = Config
    { pb_encoder  = PB_BEST
    , amk_encoder = AMK_BEST
    , amo_encoder  = AMO_BEST
    , bimander_m_is = minBound
    , bimander_m = 3
    , k_product_minimum_lit_count_for_splitting = 10
    , k_product_k = 2
    , commander_encoding_k = 3
    , max_clauses_per_constant = 1000000
    , use_formula_cache = False
    , print_used_encodings = False
    , checkForDuplicateLiterals = False
    , use_gac_binary_merge = False
    , binary_merge_no_support_for_single_bits = True
    , use_recursive_bdd_test = False
    , use_real_robdds = False
    , use_watch_dog_encoding_in_binary_merger = False
    , approximate = Nothing
    }

justApproximate :: Config -> Bool
justApproximate = isJust . approximate

approximateMaxValue :: Config -> Int
approximateMaxValue = fromMaybe 1000 . approximate

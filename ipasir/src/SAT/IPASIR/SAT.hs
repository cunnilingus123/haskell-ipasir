{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |This module provides

        1. The definition of SAT aformulas. 
        2. Variable based SAT formulas

    Definition of CNF: Every propositional formula of the form 
    $$ \\varphi = \\bigwedge_{i=1}^{n} \\bigvee_{j=1}^{m_i} (\\lnot) x_{i,j} $$
    We call a logical formula to be SAT iff the encoding is in CNF.
-}

{-# LANGUAGE StandaloneDeriving #-}
module SAT.IPASIR.SAT
    ( SAT (..)
    , VarsReduction
    , RedBoolLBool (..)
    , module Export
    , LBool(..)
    , enumToLBool
    ) where

import Data.Array (Array, bounds, ixmap, (!))
import Data.Ix (Ix(..))
import Data.Bifunctor (Bifunctor(..))
import Data.Set (Set, (\\), lookupIndex, size, toAscList)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Function (on)
import Data.List.Index (imap)

import Control.Applicative (liftA2)

import Foreign.C.Types (CInt)

import SAT.IPASIR.Literals (Literal(Variable, Allocation, unsafeReadAllocation, lit, assocs), Lit, unsign, flatLit, ByNumber)
import SAT.IPASIR.LBool (LBool(..), enumToLBool)
import SAT.IPASIR.ComplexityProblem as Export
import Data.Data (Proxy(Proxy))
import Data.Bifoldable

-- | A representative of the 
--   [SAT-Problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem)
--   with variables of type e (will be an 'Enum').
--   The 'Solution' is expressed using b (either 'Bool' or 'LBool').
--   Note that the 'Eq' instance is defined by: a == b iff every clause in a
--   is a sublist of a clause in b and vice versa.
newtype SAT e b = SAT [[e]]
    deriving (Show, Read)

newtype VarsReduction v e b = VarsReduction [Set v]


instance (Enum e, Ix e, Ord v, Num e, Integral e) => Reduction (VarsReduction v e b) where
    type CPFrom (VarsReduction v e b) = SAT (Lit v) b
    type CPTo   (VarsReduction v e b) = SAT (ByNumber e) b
    newReduction = VarsReduction []
    parseEncoding (VarsReduction l) (SAT enc) = (enc', VarsReduction l')
        where
            vars    = Set.fromList $ map unsign $ concat enc
            newVars = vars \\ Set.unions l
            enc'    = SAT $ (map . map) (toEnum . flatLit . fmap (parseLit 1 l')) enc
            l'
                | null newVars = l
 --               | Set.findMax (last l) < Set.findMin newVars = init l ++ [Set.union newVars (last l)]
                | otherwise    = newVars : l
            parseLit i (s:ss) x = case lookupIndex x s of
                Nothing -> parseLit (i + size s) ss x
                Just t  -> i + t
    parseSolution (VarsReduction l) array = Map.unions m
        where
            subMap offset set = Map.fromAscList $ imap (\i v -> (v, array ! toEnum (i+offset)) ) 
                                                $ toAscList set
            (_,m) = foldr (\set (offset, res) -> (offset + size set, subMap offset set : res)) (1,[]) l

instance Ord e => Eq (SAT e b) where
    SAT a == SAT b = on (==) (Set.fromList . map Set.fromList)  a b

instance Bifunctor SAT where
    bimap f _ (SAT cnf) = SAT $ (map . map) f cnf

instance Bifoldable SAT where
    bifoldl f _ s (SAT sat) = foldl f s $ concat sat
    bifoldr f _ s (SAT sat) = foldr f s $ concat sat

instance (Literal l) => ComplexityProblem (SAT l b) where
    type Solution (SAT l b) = Allocation l b

instance (Literal l) => AssumingProblem (SAT l b) where
    type Conflict   (SAT l b) = [Variable l]
    type Assumption (SAT l b) = l

instance (Literal l) => Solutiontransform (SAT l Bool) where
    solutionToEncoding    sol = SAT  [[lit b v]      | (v,b) <- assocs (Proxy :: Proxy l) sol ]
    negSolutionToEncoding sol = SAT [[ lit (not b) v | (v,b) <- assocs (Proxy :: Proxy l) sol ]]

instance (Literal l) => Solutiontransform (SAT l LBool) where
    solutionToEncoding sol = SAT $ map pure $ do
        (v,b) <- assocs (Proxy :: Proxy l) sol
        case b of
            LUndef -> []
            LTrue  -> [lit True  v]
            LFalse -> [lit False v]
    negSolutionToEncoding sol = SAT $ pure $ do
        (v,b) <- assocs (Proxy :: Proxy l) sol
        case b of
            LUndef -> []
            LTrue  -> [lit False v]
            LFalse -> [lit True  v] 

deriving via (BoolLBoolDerive SAT l)
    instance (Literal l) =>  Reduction (RedBoolLBool (SAT l))

deriving via (BoolLBoolDerive SAT l)
    instance (Literal l) => AReduction (RedBoolLBool (SAT l))

deriving via (LBoolTrueDerive SAT l)
    instance (Literal l) =>  Reduction (RedLBoolTrue (SAT l))

deriving via (LBoolTrueDerive SAT l)
    instance (Literal l) => AReduction (RedLBoolTrue (SAT l))

deriving via (LBoolFalseDerive SAT l)
    instance (Literal l) =>  Reduction (RedLBoolFalse (SAT l))

deriving via (LBoolFalseDerive SAT l)
    instance (Literal l) => AReduction (RedLBoolFalse (SAT l))

deriving via (EnumDerive SAT l (ByNumber e) b)
    instance (Literal l, Literal (ByNumber e), Ix e, Integral e) =>  Reduction (RedEnum SAT l (ByNumber e) b)

deriving via (EnumDerive SAT l (ByNumber e) b)
    instance (Literal l, Literal (ByNumber e), Ix e, Integral e) => AReduction (RedEnum SAT l (ByNumber e) b)


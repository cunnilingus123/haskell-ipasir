{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}

{- |This module provides

        1. The definition of SAT aformulas. 
        2. Variable based SAT formulas

    Definition of CNF: Every propositional formula of the form 
    $$ \\varphi = \\bigwedge_{i=1}^{n} \\bigvee_{j=1}^{m_i} (\\lnot) x_{i,j} $$
    We call a logical formula to be SAT iff the encoding is in CNF.
-}

module SAT.IPASIR.SAT
    ( SAT (..)
    , SATLit (..)
    , VarsReduction
    , RedBoolLBool (..)
    , module Export
    , LBool(..)
    , enumToLBool
    ) where

import Data.Array (Array, assocs, bounds, ixmap, (!))
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

import SAT.IPASIR.Literals (LBool(..), Lit, flatLit, extract, enumToLBool)
import SAT.IPASIR.ComplexityProblem as Export

-- | A representative of the 
--   [SAT-Problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem)
--   with variables of type e (will be an 'Enum').
--   The 'Solution' is expressed using b (either 'Bool' or 'LBool').
--   Note that the 'Eq' instance is defined by: a == b iff every clause in a
--   is a sublist of a clause in b and vice versa.
newtype SAT e b = SAT [[e]]
    deriving (Show, Read)

newtype SATLit v b = SATLit [[Lit v]]
    deriving (Show, Read)

instance Ord v => ComplexityProblem (SATLit v b) where
    type Solution (SATLit v b) = Map v b

instance Ord v => AssumingProblem (SATLit v b) where
    type Conflict   (SATLit v b) = [v]
    type Assumption (SATLit v b) = Lit v

newtype VarsReduction v e b = VarsReduction [Set v]

instance (Enum e, Ix e, Ord v) => Reduction (VarsReduction v e b) where
    type CPFrom (VarsReduction v e b) = SATLit v b
    type CPTo   (VarsReduction v e b) = SAT e b
    newReduction = VarsReduction []
    parseEncoding (VarsReduction l) (SATLit enc) = (enc', VarsReduction l')
        where
            vars = Set.fromList $ map extract $ concat enc
            newVars = vars \\ Set.unions l

            enc' = SAT $ (map . map) (toEnum . flatLit . fmap (parseLit 1 l')) enc
            l'
                | null newVars = l
 --               | Set.findMax (last l) < Set.findMin newVars = init l ++ [Set.union newVars (last l)]
                | otherwise    = newVars : l
            parseLit i (s:ss) x = case lookupIndex x s of
                Nothing -> parseLit (i + size s) ss x
                Just t  -> i + t

 --   parseSolution :: r -> Solution (CPTo r) -> Solution (CPFrom r)
    parseSolution (VarsReduction l) array = Map.unions m
        where
            subMap offset set = Map.fromAscList $ imap (\i v -> (v, array ! toEnum (i+offset)) ) 
                                                $ toAscList set
            (_,m) = foldr (\set (offset, res) -> (offset + size set, subMap offset set : res)) (1,[]) l

instance Bifunctor SATLit where
    bimap f _ (SATLit cnf) = SATLit $ (map . map . fmap) f cnf

instance Ord e => Eq (SAT e b) where
    SAT a == SAT b = on (==) (Set.fromList . map Set.fromList)  a b

instance Bifunctor SAT where
    bimap f _ (SAT cnf) = SAT $ (map . map) f cnf

instance (Enum e, Ix e) => ComplexityProblem (SAT e b) where
    type Solution (SAT e b) = Array e b

instance (Enum e, Ix e) => AssumingProblem (SAT e b) where
    type Conflict   (SAT e b) = [e]
    type Assumption (SAT e b) = e

instance (Enum e, Ix e, Num e) => Solutiontransform (SAT e LBool) where
    solutionToEncoding    = SAT . map pure .              sol2Enc ((*) . parseEnum)
    negSolutionToEncoding = SAT .     pure . map negate . sol2Enc ((*) . parseEnum)

instance (Enum e, Ix e, Num e) => Solutiontransform (SAT e Bool) where
    solutionToEncoding    = SAT . map pure              . sol2Enc ((*) . pred . (*2) . parseEnum)
    negSolutionToEncoding = SAT .     pure . map negate . sol2Enc ((*) . pred . (*2) . parseEnum)

parseEnum :: (Enum a, Enum b) => a -> b
parseEnum = toEnum . fromEnum

sol2Enc :: (Enum e, Ix e, Num e, Enum b) => (b -> e -> e) -> Array e b -> [e]
sol2Enc f = filter (/=0) . map (uncurry (flip f)) . assocs

deriving via (BoolLBoolDerive SAT e)
    instance (Enum e, Ix e) =>  Reduction (RedBoolLBool (SAT e))

deriving via (BoolLBoolDerive SAT e)
    instance (Enum e, Ix e) => AReduction (RedBoolLBool (SAT e))

deriving via (BoolLBoolDerive SATLit v)
    instance (Ord v) =>  Reduction (RedBoolLBool (SATLit v))

deriving via (BoolLBoolDerive SATLit v)
    instance (Ord v) => AReduction (RedBoolLBool (SATLit v))

deriving via (LBoolTrueDerive SAT e)
    instance (Enum e, Ix e) =>  Reduction (RedLBoolTrue (SAT e))

deriving via (LBoolTrueDerive SAT e)
    instance (Enum e, Ix e) => AReduction (RedLBoolTrue (SAT e))

deriving via (LBoolTrueDerive SATLit v)
    instance (Ord v) =>  Reduction (RedLBoolTrue (SATLit v))

deriving via (LBoolTrueDerive SATLit v)
    instance (Ord v) => AReduction (RedLBoolTrue (SATLit v))

deriving via (LBoolFalseDerive SAT e)
    instance (Enum e, Ix e) =>  Reduction (RedLBoolFalse (SAT e))

deriving via (LBoolFalseDerive SAT e)
    instance (Enum e, Ix e) => AReduction (RedLBoolFalse (SAT e))

deriving via (LBoolFalseDerive SATLit v)
    instance (Ord v) =>  Reduction (RedLBoolFalse (SATLit v))

deriving via (LBoolFalseDerive SATLit v)
    instance (Ord v) => AReduction (RedLBoolFalse (SATLit v))

deriving via (EnumDerive SAT e i b)
    instance (Enum e, Ix e, Enum i, Ix i) =>  Reduction (RedEnum SAT e i b)

deriving via (EnumDerive SAT e i b)
    instance (Enum e, Ix e, Enum i, Ix i) => AReduction (RedEnum SAT e i b)

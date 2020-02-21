{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

{- |This module provides

        1. The definition of XSAT formulas. 
        2. Variable based XSAT formulas

    Definition of XCNF: Every propositional formula of the form 
    $$ \\varphi = cnf \\wedge \\underbrace{\\bigwedge_{i=1}^{n} \\left( (\\lnot) \\bigoplus_{j=1}^{m_i} x_{i,j} \\right)}_{\\text{xnf}} $$
    where \\( cnf \\) is a CNF and \\( \\oplus \\) is the exclusive or. Note, that the xnf is a gaussian system.
    We call a logical formula to be XSAT iff the encoding is in XCNF.
-}

module SAT.IPASIR.XSAT where

import Data.Map (Map)
import Data.Ix (Ix)
import Data.Array (Array)
import Data.Bifunctor (Bifunctor(..))

import SAT.IPASIR.SAT
import SAT.IPASIR.Literals

-- | Like the 'ComplexityProblem' 'SAT', but with an additional gaussian system.
data XSAT e b = XSAT [[e]] [[e]]
    deriving (Show, Read)

satToXsat :: SAT e b -> XSAT e b
satToXsat (SAT f) = XSAT f []

-- | Like the 'ComplexityProblem' 'SATLit', but with an additional gaussian system.
--   'Lit [v]' is a row in the gaussian system. 'Pos [ a,b,c ]' means
--   $$ a \\oplus b \\oplus c = 1 $$
--   and 'Neg [ a,b,c ]' means
--   $$ a \\oplus b \\oplus c = 0 $$
data XSATLit v b = XSATLit [[Lit v]] [Lit [v]]
    deriving (Show, Read)

satlitToXsatlit :: SATLit v b -> XSATLit v b
satlitToXsatlit (SATLit f) = XSATLit f []

data SatToXSatRed  sat = SatToXSatRed

data XSatToSatRed xsat = XSatToSatRed

instance (Enum e, Ix e) => ComplexityProblem (XSAT e b) where
    type Solution (XSAT e b) = Array e b

instance (Enum e, Ix e) => AssumingProblem (XSAT e b) where
    type Conflict   (XSAT e b) = [e]
    type Assumption (XSAT e b) = e

instance Bifunctor XSAT where
    first  f (XSAT cnf xnf) = XSAT ((map . map) f cnf) ((map . map) f xnf)
    second _ (XSAT cnf xnf) = XSAT cnf xnf

instance Ord v => ComplexityProblem (XSATLit v b) where
    type Solution (XSATLit v b) = Map v b

instance Ord v => AssumingProblem (XSATLit v b) where
    type Conflict   (XSATLit v b) = [v]
    type Assumption (XSATLit v b) = Lit v

instance Bifunctor XSATLit where
    first  f (XSATLit cnf xnf) = XSATLit ((map . map . fmap) f cnf) ((map . fmap . map) f xnf)
    second _ (XSATLit cnf xnf) = XSATLit cnf xnf

instance (Enum e, Ix e) => Reduction (SatToXSatRed (SAT e b)) where
    type CPFrom (SatToXSatRed (SAT e b)) =  SAT e b
    type CPTo   (SatToXSatRed (SAT e b)) = XSAT e b
    newReduction = SatToXSatRed
    parseEncoding _ sat = (satToXsat sat, SatToXSatRed)
    parseSolution _ = id

instance (Enum e, Ix e) => AReduction (SatToXSatRed (SAT e b)) where
    parseAssumption _ = pure
    parseConflict _   = id

instance (Ord v) => Reduction (SatToXSatRed (SATLit v b)) where
    type CPFrom (SatToXSatRed (SATLit v b)) =  SATLit v b
    type CPTo   (SatToXSatRed (SATLit v b)) = XSATLit v b
    newReduction = SatToXSatRed
    parseEncoding _ sat = (satlitToXsatlit sat, SatToXSatRed)
    parseSolution _ = id

instance (Ord v) => AReduction (SatToXSatRed (SATLit v b)) where
    parseAssumption _ = pure
    parseConflict _   = id

instance (Enum e, Ix e) => Reduction (XSatToSatRed (XSAT e b)) where
    type CPFrom (XSatToSatRed (XSAT e b)) = XSAT e b
    type CPTo   (XSatToSatRed (XSAT e b)) =  SAT e b
    newReduction = XSatToSatRed
    parseEncoding _ (XSAT cnf xnf) = (undefined, XSatToSatRed)
    parseSolution _ = id

instance (Enum e, Ix e) => AReduction (XSatToSatRed (XSAT e b)) where
    parseAssumption _ = pure
    parseConflict _   = id

instance (Ord v) => Reduction (XSatToSatRed (XSATLit v b)) where
    type CPFrom (XSatToSatRed (XSATLit v b)) = XSATLit v b
    type CPTo   (XSatToSatRed (XSATLit v b)) =  SATLit v b
    newReduction = XSatToSatRed
    parseEncoding _ (XSATLit cnf xnf) = (undefined, XSatToSatRed)
    parseSolution _ = id

instance (Ord v) => AReduction (XSatToSatRed (XSATLit v b)) where
    parseAssumption _ = pure
    parseConflict _   = id

deriving via (BoolLBoolDerive XSAT e)
    instance (Enum e, Ix e) =>  Reduction (RedBoolLBool (XSAT e))

deriving via (BoolLBoolDerive XSAT e)
    instance (Enum e, Ix e) => AReduction (RedBoolLBool (XSAT e))

deriving via (BoolLBoolDerive XSATLit v)
    instance (Ord v) =>  Reduction (RedBoolLBool (XSATLit v))

deriving via (BoolLBoolDerive XSATLit v)
    instance (Ord v) => AReduction (RedBoolLBool (XSATLit v))

deriving via (LBoolTrueDerive XSAT e)
    instance (Enum e, Ix e) =>  Reduction (RedLBoolTrue (XSAT e))

deriving via (LBoolTrueDerive XSAT e)
    instance (Enum e, Ix e) => AReduction (RedLBoolTrue (XSAT e))

deriving via (LBoolTrueDerive XSATLit v)
    instance (Ord v) =>  Reduction (RedLBoolTrue (XSATLit v))

deriving via (LBoolTrueDerive XSATLit v)
    instance (Ord v) => AReduction (RedLBoolTrue (XSATLit v))

deriving via (LBoolFalseDerive XSAT e)
    instance (Enum e, Ix e) =>  Reduction (RedLBoolFalse (XSAT e))

deriving via (LBoolFalseDerive XSAT e)
    instance (Enum e, Ix e) => AReduction (RedLBoolFalse (XSAT e))

deriving via (LBoolFalseDerive XSATLit v)
    instance (Ord v) =>  Reduction (RedLBoolFalse (XSATLit v))

deriving via (LBoolFalseDerive XSATLit v)
    instance (Ord v) => AReduction (RedLBoolFalse (XSATLit v))

deriving via (EnumDerive XSAT e i b)
    instance (Enum e, Ix e, Enum i, Ix i) =>  Reduction (RedEnum XSAT e i b)

deriving via (EnumDerive XSAT e i b)
    instance (Enum e, Ix e, Enum i, Ix i) => AReduction (RedEnum XSAT e i b)

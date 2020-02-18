{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

{- |This module provides

        1. The definition of XSAT formulas. 
        2. Variable based XSAT formulas

    Definition of XCNF: Every propositional formula of the form 
    $$ \\varphi = cnf \\wedge \\underbrace{\\bigwedge_{i=1}^{n} \\left( (\\lnot) \\bigoplus_{j=1}^{m_i} x_{i,j} \\right)}_{\\text{Gaussian system}} $$
    where \\( cnf \\) is a CNF and \\( \\oplus \\) is the exclusive or. 
    We call a logical formula to be XSAT iff the encoding is in XCNF.
-}

import Data.Map (Map)

import SAT.IPASIR.SAT
import SAT.IPASIR.Literals

data XSAT e b = XSAT [[e]] [[e]]
    deriving (Show, Read)

satToXsat :: SAT e b -> XSAT e b
satToXsat (SAT f) = XSAT f []

data XSATLit v b = XSATLit [[Lit v]] [Lit [v]]
    deriving (Show, Read)

satlitToXsatlit :: SATLit v b -> XSATLit v b
satlitToXsatlit (SATLit f) = XSATLit f []

instance Ord v => ComplexityProblem (XSATLit v b) where
    type Solution (XSATLit v b) = Map v b

instance Ord v => AssumingProblem (XSATLit v b) where
    type Conflict   (XSATLit v b) = [v]
    type Assumption (XSATLit v b) = Lit v

data XSatToSatRed = XSatToSatRed


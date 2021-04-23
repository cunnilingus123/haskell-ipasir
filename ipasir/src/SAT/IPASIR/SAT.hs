{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |This module provides the definition of SAT formulas. 

    Definition of CNF: Every propositional formula of the form 
    $$ \\varphi = \\bigwedge_{i=1}^{n} \\bigvee_{j=1}^{m_i} (\\lnot) x_{i,j} $$
    We call a logical formula to be SAT iff the encoding is in CNF.
-}

{-# LANGUAGE StandaloneDeriving #-}
module SAT.IPASIR.SAT
    ( SAT (..)
    , RedBoolLBool (..)
    , module Export
    ) where

import Data.Ix (Ix(..))
import Data.Proxy (Proxy(Proxy))
import Data.List (transpose)
import Data.Bifunctor (Bifunctor(bimap))
import Data.Bifoldable (Bifoldable(bifoldl, bifoldr))

import SAT.IPASIR.ComplexityProblem as Export
import SAT.IPASIR.Literals (Literal(Allocation, Variable, lit, assocs), ByNumber, litSatisfied)
import SAT.IPASIR.LBool (BoolLike(ltrue, lfalse, lnot))
import SAT.IPASIR.Foldable (foldl2D, foldr2D)

-- | A representative of the 
--   [SAT-Problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem)
--   with variables of type e (will be an 'Enum').
--   The 'Solution' is expressed using b (either 'Bool' or 'LBool').
--   Note that the 'Eq' instance is defined by: a == b iff every clause in a
--   is a sublist of a clause in b and vice versa.
newtype SAT e b = SAT [[e]]
    deriving (Show, Read)

instance Bifunctor SAT where
    bimap f _ (SAT cnf) = SAT $ (map . map) f cnf

instance Bifoldable SAT where
    bifoldl f _ s (SAT sat) = foldl2D f s sat
    bifoldr f _ s (SAT sat) = foldr2D f s sat

instance (Literal l) => ComplexityProblem (SAT l b) where
    type Solution (SAT l b) = Allocation l b

instance (Literal l, BoolLike b) => NPProblem (SAT l b) where
    checkModel sol (SAT sat) = all (any (litSatisfied sol)) sat

instance (Literal l) => AssumingProblem (SAT l b) where
    type Conflict   (SAT l b) = [Variable l]
    type Assumption (SAT l b) = l

instance (Literal l, BoolLike b) => Solutiontransform (SAT l b) where
    solutionToEncoding    sol = SAT             [intoLit b v        | (v,b) <- assocs (Proxy :: Proxy l) sol ]
    negSolutionToEncoding sol = SAT $ transpose [intoLit (lnot b) v | (v,b) <- assocs (Proxy :: Proxy l) sol ]

intoLit :: (Literal l, BoolLike b) => b -> Variable l -> [l]
intoLit b v = [ lit True  v | b == ltrue  ] ++ [ lit False v | b == lfalse ]

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


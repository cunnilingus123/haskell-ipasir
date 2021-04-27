{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

{- |This module provides the definition of 'XSAT' formulas and reductions from and to 'SAT' formulas. 

    Definition of XSAT: Every propositional formula \\( \\varphi \\) of the form 
    $$ \\varphi = \\text{xcnf} = \\text{cnf} \\wedge \\text{xnf} $$
    where
    $$ \\begin{align*}  
         \\text{cnf} &= \\bigwedge_{i=1}^{n}  \\bigvee_{j=1}^{m_i}    (\\lnot) x_{i,j} \\\\ 
         \\text{xnf} &= \\bigwedge_{i=1}^{n'} \\bigoplus_{j=1}^{m'_i} (\\lnot) x'_{i,j}
       \\end{align*}
    $$ 
    \\( \\bigoplus \\) is the logical xor.

    Note, that the cnf is a standard [SAT](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem) formula and xnf is 
    a [linear system](https://en.wikipedia.org/wiki/System_of_linear_equations) over the the [binary field](https://en.wikipedia.org/wiki/GF\(2\)) \\( GF(2) = (\\{0,1\\}, \\oplus, \\wedge) \\). 
-}

module SAT.IPASIR.XSAT 
    ( XSAT(..)
    , SatToXSatRed(..)
    , XSatToSatRed(..)
    , lineUp
    ) where

import Data.Ix (Ix)
import Data.Function (on)
import Data.Bifunctor (Bifunctor(first, second))
import Data.List (partition, sort, minimumBy)

import SAT.IPASIR.SAT 
import SAT.IPASIR.LBool (BoolLike(boolToBoolLike, (++*), lxor))
import SAT.IPASIR.Literals (Literal(Allocation, Variable, lit, unsign, isPositive), ByNumber, litSatisfied, isNegative)
import SAT.IPASIR.Foldable (foldl2D, foldr2D)
import Data.Bifoldable (Bifoldable(bifoldl, bifoldr))

-- | Like the 'ComplexityProblem' 'SAT', but with an additional system of linear equations.
data XSAT l b = XSAT [[l]] [[l]]
    deriving (Show, Read)

data SatToXSatRed sat  = SatToXSatRed
    deriving (Show, Eq)

data XSatToSatRed xsat = XSatToSatRed
    deriving (Show, Eq)

satToXsat :: SAT e b -> XSAT e b
satToXsat (SAT f) = XSAT f []

instance (Literal l) => ComplexityProblem (XSAT l b) where
    type Solution (XSAT l b) = Allocation l b

instance (Literal l, BoolLike b) => NPProblem (XSAT l b) where
    checkModel sol (XSAT cnf xnf) = checkModel sol (SAT cnf) && all (lxor . map (litSatisfied sol)) xnf

instance (Literal l, BoolLike b) => Solutiontransform (XSAT l b) where
    solutionToEncoding    = satToXsat . solutionToEncoding 
    negSolutionToEncoding = satToXsat . negSolutionToEncoding 

instance (Literal l) => AssumingProblem (XSAT l b) where
    type Conflict   (XSAT l b) = [Variable l]
    type Assumption (XSAT l b) = l

instance Bifunctor XSAT where
    first  f (XSAT cnf xnf) = XSAT ((map . map) f cnf) ((map . map) f xnf)
    second _ (XSAT cnf xnf) = XSAT cnf xnf

instance Bifoldable XSAT where
    bifoldl f _ s (XSAT cnf xnf) = foldl2D f (foldl2D f s cnf) xnf
    bifoldr f _ s (XSAT cnf xnf) = foldr2D f (foldr2D f s xnf) cnf

instance (Literal l) => Reduction (SatToXSatRed (SAT l b)) where
    type CPFrom (SatToXSatRed (SAT l b)) =  SAT l b
    type CPTo   (SatToXSatRed (SAT l b)) = XSAT l b
    newReduction = SatToXSatRed
    parseEncoding _ sat = (satToXsat sat, SatToXSatRed)
    parseSolution _ = id

instance (Literal l) => AReduction (SatToXSatRed (SAT l b)) where
    parseAssumption _ = pure
    parseConflict _   = id

instance (Literal l) => Reduction (XSatToSatRed (XSAT l b)) where
    type CPFrom (XSatToSatRed (XSAT l b)) = XSAT l b
    type CPTo   (XSatToSatRed (XSAT l b)) =  SAT l b
    newReduction = XSatToSatRed
    parseEncoding _ xsat = (xsatToSat xsat, XSatToSatRed)
    parseSolution _ = id

instance (Literal l) => AReduction (XSatToSatRed (XSAT l b)) where
    parseAssumption _ = pure
    parseConflict _   = id

deriving via (BoolLBoolDerive XSAT l)
    instance (Literal l) =>  Reduction (RedBoolLBool (XSAT l))

deriving via (BoolLBoolDerive XSAT l)
    instance (Literal l) => AReduction (RedBoolLBool (XSAT l))

deriving via (LBoolTrueDerive XSAT l)
    instance (Literal l) =>  Reduction (RedLBoolTrue (XSAT l))

deriving via (LBoolTrueDerive XSAT l)
    instance (Literal l) => AReduction (RedLBoolTrue (XSAT l))

deriving via (LBoolFalseDerive XSAT l)
    instance (Literal l) =>  Reduction (RedLBoolFalse (XSAT l))

deriving via (LBoolFalseDerive XSAT l)
    instance (Literal l) => AReduction (RedLBoolFalse (XSAT l))

deriving via (EnumDerive XSAT l (ByNumber e) b)
    instance (Literal l, Literal (ByNumber e), Ix e, Integral e) =>  Reduction (RedEnum XSAT l (ByNumber e) b)

deriving via (EnumDerive XSAT l (ByNumber e) b)
    instance (Literal l, Literal (ByNumber e), Ix e, Integral e) => AReduction (RedEnum XSAT l (ByNumber e) b)

xsatToSat :: Literal l => XSAT l b -> SAT l b
xsatToSat (XSAT cnf xnf) = case gaussJordan $ map lineUp xnf of
    Nothing -> SAT [[]]
    Just xnf' -> SAT $ cnf ++ (fullXClauseToSAT =<< xnf')

fullXClauseToSAT :: forall l. Literal l => ([Variable l], Bool) -> [[l]]
fullXClauseToSAT ([x], b)  = [[lit b x]]
fullXClauseToSAT (x:xs, b) = negativeWay ++ positiveWay
    where
        negativeWay = (lit True  x :) <$> fullXClauseToSAT (xs, b)
        positiveWay = (lit False x :) <$> fullXClauseToSAT (xs, not b)

lineUp :: Literal l => [l] -> ([Variable l], Bool)
lineUp l = (oddTimes $ map unsign l , not $ lxor $ map isNegative l)

gaussJordan :: Ord v => [([v], Bool)] -> Maybe [([v], Bool)]
gaussJordan l = jordan <$> gauss l

jordan :: Ord v => [([v], Bool)] -> [([v], Bool)]
jordan []     = []
jordan (x:xs) = go x xs : jordan xs
    where
        go :: Ord v => ([v], Bool) -> [([v], Bool)] -> ([v], Bool)
        go x@(a:as,bool) gauss@(y@(b:bs,_):ys)
            | a == b    = go (symmetricDifference x y) ys
            | a <  b    = first (a:) $ go (as,bool) gauss
            | otherwise = go x ys
        go x _ = x

gauss :: Ord v => [([v], Bool)] -> Maybe [([v], Bool)]
gauss l
    | any snd trivs = Nothing -- Not a solvable gaussian system
    | null l'       = Just [] 
    | otherwise     = (minL :) <$> gauss (has' ++ hasnt)
    where
        (trivs,l')   = partition (null . fst) l 
        minL         = minLine l'
        minV         = head $ fst minL
        (has, hasnt) = partition (hasElement minV) l'
        has'         = symmetricDifference minL <$> tail has

-- | Sorts the list and removes every element, with an even occurance in the list.
--   the Result doesnt have dublicates.
--   > oddTimes [3,1,2,1,2,1,6] == [1,3,6]
oddTimes :: Ord v => [v] -> [v]
oddTimes = oddTimes' . sort
    where
        oddTimes' []  = []
        oddTimes' [x] = [x]
        oddTimes' (x:y:xs)
            | x == y    =     oddTimes' xs
            | otherwise = x : oddTimes' (y:xs)

minLine :: Ord v => [([v],Bool)] -> ([v],Bool)
minLine = minimumBy (compare `on` head . fst)

hasElement :: Ord v => v -> ([v], Bool) -> Bool
hasElement x ([],_)    = False
hasElement x (a:as,_)
    | x <  a    = False
    | x == a    = True
    | otherwise = hasElement x (as,True)

-- | Only works on ordered lists without doublicates. See 
--   [Wikipedia: symmetric difference](https://en.wikipedia.org/wiki/Symmetric_difference) 
--   for further information.
symmetricDifference :: Ord v => ([v], Bool) -> ([v], Bool) -> ([v], Bool)
symmetricDifference (xs,xb) (ys,yb) = (symmetricDifference' xs ys, xb ++* yb)
    where
        symmetricDifference' [] ys = ys
        symmetricDifference' xs [] = xs
        symmetricDifference' (x:xs) (y:ys) = case compare x y of
            LT -> x : symmetricDifference' xs (y:ys)
            GT -> y : symmetricDifference' (x:xs) ys
            _  -> symmetricDifference' xs ys

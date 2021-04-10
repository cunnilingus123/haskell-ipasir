{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

{- |This module provides

        1. The definition of XSAT formulas. 
        2. Variable based XSAT formulas

    Definition of XCNF: Every propositional formula of the form 
    $$ \\varphi = cnf \\wedge \\underbrace{\\bigwedge_{i=1}^{n} 
       \\left( (\\lnot) \\bigoplus_{j=1}^{m_i} x_{i,j} \\right)}_{\\text{xnf}} $$
    where \\( cnf \\) is a CNF and \\( \\oplus \\) is the exclusive or.
    Note, that the xnf is a gaussian system.
    We call a logical formula to be XSAT iff the encoding is in XCNF.
-}

module SAT.IPASIR.XSAT where

import Data.Map (Map)
import Data.Ix (Ix)
import Data.Array (Array)
import Data.Function (on)
import Data.Bifunctor (Bifunctor(..))
import Data.Set (Set, fromList, toList, member, fromAscList)
import Data.List (sort, minimumBy, partition)
import Data.Bits ((.|.), (.&.), bit, xor)

import SAT.IPASIR.SAT
import SAT.IPASIR.Literals
import SAT.IPASIR.Foldable (foldl2D, foldr2D)
import Data.Bifoldable (Bifoldable(..))

-- | Like the 'ComplexityProblem' 'SAT', but with an additional gaussian system.
data XSAT l b = XSAT [[l]] [[l]]
    deriving (Show, Read)

data SatToXSatRed sat = SatToXSatRed

satToXsat :: SAT e b -> XSAT e b
satToXsat (SAT f) = XSAT f []

xlitsToClause :: [Lit v] -> Lit [v]
xlitsToClause = xlitsToClause' False []
    where
        xlitsToClause' :: Bool -> [v] -> [Lit v] -> Lit [v]
        xlitsToClause' False l [] = Pos l
        xlitsToClause' _     l [] = Neg l
        xlitsToClause' b     l (Pos x: xs) = xlitsToClause'      b  (x:l) xs
        xlitsToClause' b     l (Neg x: xs) = xlitsToClause' (not b) (x:l) xs

instance (Literal l) => ComplexityProblem (XSAT l b) where
    type Solution (XSAT l b) = Allocation l b

instance (Literal l) => AssumingProblem (XSAT l b) where
    type Conflict   (XSAT l b) = [Variable l]
    type Assumption (XSAT l b) = l

instance Bifunctor XSAT where
    first  f (XSAT cnf xnf) = XSAT ((map . map) f cnf) ((map . map) f xnf)
    second _ (XSAT cnf xnf) = XSAT cnf xnf

instance Bifoldable XSAT where
    bifoldl f s (XSAT cnf xnf) = foldl2D f (foldl2D f s cnf) xnf
    bifoldr f s (XSAT cnf xnf) = foldr2D f (foldr2D f s xnf) cnf

instance (Literal l) => Reduction (SatToXSatRed (SAT l b)) where
    type CPFrom (SatToXSatRed (SAT l b)) =  SAT l b
    type CPTo   (SatToXSatRed (SAT l b)) = XSAT l b
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
    parseEncoding _ xsat = (fullXSATToSat xsat, XSatToSatRed)
    parseSolution _ = id

instance (Enum e, Ix e) => AReduction (XSatToSatRed (XSAT e b)) where
    parseAssumption _ = pure
    parseConflict _   = id

instance (Ord v) => Reduction (XSatToSatRed (XSATLit v b)) where
    type CPFrom (XSatToSatRed (XSATLit v b)) = XSATLit v b
    type CPTo   (XSatToSatRed (XSATLit v b)) =  SATLit v b
    newReduction = XSatToSatRed
    parseEncoding _ xsat = (fullXSATLitToSatLit xsat, XSatToSatRed)
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

fullXSATToSat :: Enum e => XSAT e b -> SAT e b
fullXSATToSat xsat = first (toEnum . flatLit) $ SAT cnf'
    where
        XSAT cnf xnf = first (parseEnum . fromEnum) xsat
        parseEnum i
            | i > 0 = Pos i
            | i < 0 = Neg $ negate i
        SATLit cnf' = fullXSATLitToSatLit $ XSATLit cnf $ map sequence xnf

fullXSATLitToSatLit :: forall v b. Ord v => XSATLit v b -> SATLit v b
fullXSATLitToSatLit (XSATLit cnf xnf) = SATLit $ cnf'' ++ cnf'
    where
        (xnf', trivials) = gaussJordan xnf
        cnf' :: [[Lit v]]
        cnf' = fullXClauseToSAT =<< xnf' ++ trivials

        replacings :: [(Lit v, Lit v)]
        replacings = h =<< trivials

        cnf'' :: [[Lit v]]
        cnf'' = foldl (\cnf r -> (map . map) (`replace` r) cnf) cnf replacings

        replace :: Lit v -> (Lit v, Lit v) -> Lit v
        replace lit (x,y)
            | lit == x  = y
            | otherwise = lit

        h :: ([v],Bool) -> [(Lit v, Lit v)]
        h ([x,y],False) = [(Neg x, Neg y),(Pos x, Pos y)]
        h ([x,y],True ) = [(Neg x, Pos y),(Pos x, Neg y)]
        h _ = []


fullXClauseToSAT :: ([v], Bool) -> [[Lit v]]
fullXClauseToSAT ([x], True)  = [[Pos x]]
fullXClauseToSAT ([x], False) = [[Neg x]]
fullXClauseToSAT (x:xs, b) = negativeWay ++ positiveWay
    where
        negativeWay = (Neg x :) <$> fullXClauseToSAT (xs, b)
        positiveWay = (Pos x :) <$> fullXClauseToSAT (xs, not b)

-- | Gauss elimination
gaussElemination :: forall v. Ord v => [Lit [v]] -> [([v], Bool)]
gaussElemination l = gaussElemination' $ map sorted l
    where
        sorted :: Lit [v] -> ([v], Bool)
        sorted l = (oddTimes (unsign l), isPositive l)
        gaussElemination' :: [([v], Bool)] -> [([v], Bool)]
        gaussElemination' l
            | null l'   = []
            | otherwise = m : gaussElemination' l''
            where
                l'  = filter filt l
                l'' = symmetricDifferenceIf m <$> l'
                m = minLine l'
                filt :: ([v], Bool) -> Bool
                filt ([],False) = False
                filt ([],_)     = error "Not a solvable Gaussian system"
                filt _          = True


jordan :: Ord v => [([v], Bool)] -> [([v], Bool)]
jordan = jordan' . reverse
    where

        jordan' :: Ord v => [([v], Bool)] -> [([v], Bool)]
        jordan' = foldl (\res x -> line (x : res) : res ) []

        line :: Ord v => [([v], Bool)] -> ([v], Bool)
        line [x] = x
        line (x@(v,b):y:xs) = first (lhs++) $ line (x':xs)
            where
                (lhs, rhs) = span (< head (fst y)) v
                x' = symmetricDifferenceIf y (rhs, b)


gaussJordan :: Ord v => [Lit [v]] -> ([([v], Bool)], [([v], Bool)] )
gaussJordan sys = (sys'', trivials' ++ trivials'')
    where
        (sys' , trivials' ) = minimizeSmallLines $ gaussElemination sys
        (sys'', trivials'') = minimizeSmallLines $ jordan sys'


minimizeSmallLines :: Ord v => [([v], Bool)] -> ([([v], Bool)], [([v], Bool)] )
minimizeSmallLines l = case smallClause l Nothing of
    Nothing -> (l, [])
    Just x  -> second (x:) $ minimizeSmallLines 
                           $ filter (not . null . fst) 
                           $ map (symmetricDifferenceIf x) l
    where
        smallClause :: [([v], Bool)] -> Maybe ([v], Bool) -> Maybe ([v], Bool)
        smallClause [] r = r
        smallClause (x:xs) r = case x of
            ([_]  ,_) -> Just x
            ([_,_],_) -> smallClause xs (Just x)
            _         -> smallClause xs r

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

-- | Only works on ordered lists without doublicates.
symmetricDifferenceIf :: Ord v => ([v], Bool) -> ([v], Bool) -> ([v], Bool)
symmetricDifferenceIf x y
    | b (fst y) = symmetricDifference x y
    | otherwise = y
    where
        h = head $ fst x
        b [] = False
        b (y:ys) = case compare y h of
            LT -> b ys
            EQ -> True
            _  -> False

-- | Only works on ordered lists without doublicates. See 
--   [Wikipedia: symmetric difference](https://en.wikipedia.org/wiki/Symmetric_difference) 
--   for further information.
symmetricDifference :: Ord v => ([v], Bool) -> ([v], Bool) -> ([v], Bool)
symmetricDifference (xs,xb) (ys,yb) = (symmetricDifference' xs ys, xor xb yb)
    where
        symmetricDifference' [] ys = ys
        symmetricDifference' xs [] = xs
        symmetricDifference' (x:xs) (y:ys) = case compare x y of
            LT -> x : symmetricDifference' xs (y:ys)
            GT -> y : symmetricDifference' (x:xs) ys
            _  -> symmetricDifference' xs ys

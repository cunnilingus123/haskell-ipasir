module SAT.IPASIR.Clauses where

import SAT.IPASIR.Literals
import Data.Graph.Inductive.Query.Monad
import Data.Maybe

data Clause v      = Or (OrClause v) | XOr (XOrClause v)
    deriving (Show, Eq, Ord)

type EClause v     = Clause (Ext v)

type OrClause v    = [Lit v]
type XOrClause v   = Lit [v]

type EOrClause v   = [ELit v]
type EXOrClause v  = Lit [Ext v]

type NormalForm v  = ([OrClause v], [XOrClause v])
type ENormalForm v = ([EOrClause v], [EXOrClause v])

type CNF v         = [ OrClause v]
type ECNF v        = [EOrClause v]

getLits :: Clause v -> [Lit v]
getLits ( Or a) = a
getLits (XOr a) = map Pos $ ordinal a

partitionClauses :: Bool -> [Clause v] -> ([OrClause v],[XOrClause v])
partitionClauses _     []          = ([],[])
partitionClauses True  (Or x:xs) = mapFst (x:) $ partitionClauses True xs
partitionClauses False (XOr x:xs)= mapSnd (x:) $ partitionClauses False xs
partitionClauses _ (Or [x]:xs)   = mapSnd ((return <$> x) :) $ partitionClauses False xs  -- ( ors, (return <$> x) : xors)
partitionClauses _ (Or x:xs)     = mapFst (x:) $ partitionClauses False xs
partitionClauses _ ((XOr x):xs)          
    | isJust transformed = mapFst (fromJust transformed:) $ partitionClauses True xs
    | otherwise          = mapSnd (x:) $ partitionClauses True xs
    where
        transformed    = transform vars
        vars = ordinal x
        transform :: [v] -> Maybe [Lit v]
        transform []  = Just []
        transform [a] = Just [ const a <$> (fromBool $ sign x) ]
        transform _   = Nothing
        


evenToCNF' :: Bool -> Int -> [[Bool]]
evenToCNF' False 0 = [[]]
evenToCNF' True  0 = []
evenToCNF' positive numberVars = map (False:) positives ++ map (True:) negatives
    where
        negatives = evenToCNF' (not positive) (numberVars-1)
        positives = evenToCNF' positive (numberVars-1)

evenToCNF :: Lit [a] -> [[Lit a]]
evenToCNF xclause = map (zipWith (\v b -> const v <$> fromBool b) vars) bClauses
    where
        bClauses  = evenToCNF' (sign xclause) $ length $ vars
        vars      = ordinal xclause

xclausesToCNF :: [Lit [a]] -> [[Lit a]]
xclausesToCNF = concat . map evenToCNF
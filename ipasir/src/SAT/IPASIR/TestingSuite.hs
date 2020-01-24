{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SAT.IPASIR.TestingSuite where

import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import GHC.TypeNats
import Data.Proxy
import Control.Monad 
import Data.List
import Data.Reflection
import Data.Maybe

import SAT.IPASIR.Solver
import SAT.IPASIR.ComplexityProblem

-- Assumption restrictions
data AssumptionRestriction 
    = NoAssumption 
    | SingleAssumtionBeforeSolve
    | MultiAssumptionBeforeSolve
    | NoAssumptionRestriction
    deriving(Show, Eq, Ord , Enum)

data VariableRestriction
    = EveryVarUsed
    | MaxVarUsed
    | NoEncodingRestriction
    deriving(Show, Eq, Ord , Enum)

data CommandMarker
    = AddEncodingMarker
    | CompleteEncodingMarker
    | AssumeSomethingMarker
    | SolveNowMarker
    deriving(Show, Eq, Ord , Enum)

data Command enc ass
    = AddEncoding enc
    | AssumeSomething ass
    | SolveNow
    deriving(Show, Eq, Ord)

newtype Program enc ass = Program [Command enc ass]
    deriving (Show, Eq, Ord)
newtype ProgramS s enc ass = ProgramS (Program enc ass)

data RefiedArbitrary enc ass = RefiedArbitrary (Gen enc) (Gen ass) ([enc] -> enc) Word AssumptionRestriction

createSatArbitrary :: forall e. (Enum e, Num e, Eq e)
                   => Word 
                   -> Word 
                   -> AssumptionRestriction 
                   -> VariableRestriction 
                   -> RefiedArbitrary [[e]] e
createSatArbitrary nVar nSolvings aRestr vRestr
    = RefiedArbitrary undefined undefined (completeEncoding vRestr) nSolvings aRestr
  where
    maxLit = toEnum $ fromEnum nVar :: e
    vars :: [[[e]]] -> [e]
    vars = map abs . concat .  concat 
    completeEncoding :: VariableRestriction -> [[[e]]] -> [[e]]
    completeEncoding EveryVarUsed          = undefined
    completeEncoding MaxVarUsed            = pure . (maxLit <$) . guard . notElem maxLit . vars
    completeEncoding NoEncodingRestriction = const []

instance (Reifies s (RefiedArbitrary enc ass)) => Arbitrary (ProgramS s enc ass) where
    arbitrary = genProgramm ra
      where
        ra = reflect (Proxy :: Proxy s)

unreflectArbi :: ProgramS s enc ass -> Proxy s -> Program enc ass
unreflectArbi (ProgramS p) _ = p

genProgramm :: forall s enc ass. 
               RefiedArbitrary enc ass 
            -> Gen (ProgramS s enc ass)
genProgramm (RefiedArbitrary encoding assumption completer n restr) = do
    block <- genCommandBlock n restr
    coms <- sequence $ parseCommand <$> block
    return $ ProgramS $ Program coms
  where
    parseCommand :: CommandMarker -> Gen (Command enc ass)
    parseCommand AddEncodingMarker     = AddEncoding     <$> encoding
    parseCommand AssumeSomethingMarker = AssumeSomething <$> assumption
    parseCommand SolveNowMarker        = return SolveNow
    parser :: [CommandMarker] -> [Command enc ass] -> Gen [Command enc ass]
    parser (CompleteEncodingMarker:xs) past = do
        rest <- mapM parseCommand xs
        let c = AddEncoding $ completer $ mapMaybe toEncoding past
        return $ past ++ c : rest
    parser (x:xs) past = parser xs =<< (:past) <$> parseCommand x
    parser _      past = pure past
    toEncoding :: Command enc ass -> Maybe enc
    toEncoding (AddEncoding e) = Just e
    toEncoding _ = Nothing

genCommandBlock :: Word -> AssumptionRestriction -> Gen [CommandMarker]
genCommandBlock n restr = do
    t <- sequence $ arbitrary <$ [0..n-1]
    s <- zipWithM (f restr) t [0..]
    pure $ resorting =<< s
  where
    assOrAdd :: Gen CommandMarker
    assOrAdd = elements [AssumeSomethingMarker, AddEncodingMarker]
    f :: AssumptionRestriction -> Word -> Word -> Gen [CommandMarker]
    f _ 0 0 = pure [CompleteEncodingMarker, SolveNowMarker]
    f _ 0 _ = pure [SolveNowMarker]
    f SingleAssumtionBeforeSolve 1 m = liftM2 (:) assOrAdd $ f SingleAssumtionBeforeSolve 0 m
    f r n m = do
        c <- if r <= SingleAssumtionBeforeSolve
            then pure AddEncodingMarker
            else assOrAdd
        (c:) <$> f r (n-1) m
    resorting :: [CommandMarker] -> [CommandMarker]
    resorting 
        | restr == MultiAssumptionBeforeSolve = sort
        | otherwise = id







{-
newtype SolverProgram a e (nSolves :: Nat) aC eC = SolverProgram [Command a e]

assumeFunction :: ComplexityProblem cp => Proxy cp -> Gen (Assumption cp)
assumeFunction = undefined
encodeFunction :: ComplexityProblem cp => Proxy cp -> Gen (Encoding cp)
encodeFunction = undefined

f :: ComplexityProblem cp => Word -> Gen [Command (Assumption cp) (Encoding cp)]
f 0 = pure [SolveNow]
f n = do 
    i <- choose (0,1)
    newCommand <- if i == 0
        then AssumeSomething <$> assumeFunction
        else AddEncoding <$> encodeFunction
    (newCommand :) $ f $ n-1

instance (KnownNat n,ComplexityProblem cp) => Arbitrary (SolverProgram a e n NoAssumptionRestriction NoEncodingRestriction) where
    arbitrary = do 
        let nSolves = natVal (Proxy :: Proxy n)
        amountCommands <- sequence $ (arbitrary :: Gen Word) <$ [1..nSolves]
        commands <- sequence $ f <$> amountCommands
        pure $ SolverProgram $ concat commands
-}
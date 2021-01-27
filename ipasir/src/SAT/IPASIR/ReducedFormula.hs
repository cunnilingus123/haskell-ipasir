{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}

module SAT.IPASIR.ReducedFormula where

import GHC.TypeLits (TypeError (..), ErrorMessage (Text))
import Data.Constraint (Constraint(..) )
import Data.List.NonEmpty (NonEmpty(..), fromList, toList )
import SAT.IPASIR.Printing
import Data.Bifunctor (first)
import Data.List (isPrefixOf)

data ReducedFormula l = RYes | RNo | ReducedFormula (Bla Other l)

data Bla (x :: BF) l = forall a. NotEqual x a => Bla (RFormula a l)

data BF = All | Any | Odd | Other

data RFormula (a :: BF) l where
    RLit :: l -> RFormula Other l
    RAll :: NonEmpty (Bla All l) -> RFormula All l
    RAny :: NonEmpty (Bla Any l) -> RFormula Any l
    ROdd :: NonEmpty (Bla Odd l) -> RFormula Odd l

type family NotEqual (a :: BF) (b :: BF) :: Constraint where
    NotEqual Other Other = ()
    NotEqual x x = TypeError (Text "Forbidden case! It is not allowed to have an All inside an All, Any inside an Any or an Odd inside on Odd if you want to create a reduced Formula.")
    NotEqual _ _ = ()

rLit :: NotEqual x Other => l -> Bla x l
rLit = Bla . RLit

rAll :: NotEqual x All => NonEmpty (Bla All l) -> Bla x l
rAll = Bla . RAll

rAny :: NotEqual x Any => NonEmpty (Bla Any l) -> Bla x l
rAny = Bla . RAny

rOdd :: NotEqual x Odd => NonEmpty (Bla Odd l) -> Bla x l
rOdd = Bla . ROdd

tester 
  = RAll $ fromList
    [ rAny $ fromList [rLit 2, rLit 3] 
    , rOdd $ fromList [rLit 2, rLit 3]
  --  , rAll [rLit 2, rLit 3]
    ]

instance Show l => Show (ReducedFormula l) where
    show RYes = "YES"
    show RNo  = "NO"
    show (ReducedFormula f) = show f

instance Show l => Show (RFormula a l) where
    show f = show $ toPrinter f
        where
            toPrinter :: Show l => RFormula x l -> Printer
            toPrinter (RLit l) = Terminal $ show l
            toPrinter (RAll l) = Roundup "ALL" $ map (\(Bla x) -> toPrinter x) $ toList l
            toPrinter (RAny l) = Roundup "ANY" $ map (\(Bla x) -> toPrinter x) $ toList l
            toPrinter (ROdd l) = Roundup "ODD" $ map (\(Bla x) -> toPrinter x) $ toList l

instance Show l => Show (Bla a l) where
    show (Bla f) = show f

instance (Read l) => Read (ReducedFormula l) where
    readsPrec i str
        | "YES" `isPrefixOf` str = [(RYes, drop 3 str)]
        | "NO"  `isPrefixOf` str = [(RNo,  drop 2 str)]
        | otherwise            = do
            (printer,r) <- readsPrec i str
            let f = case printer of
                    (Terminal s)  -> ReducedFormula $ Bla $ parseOther printer
                    (Roundup s l) -> case s of
                        "ODD" -> ReducedFormula $ Bla $ parseOdd printer
                        "ALL" -> ReducedFormula $ Bla $ parseAll printer
                        "ANY" -> ReducedFormula $ Bla $ parseAny printer
            return (f,r)

instance (Read l) => Read (RFormula Other l) where
    readsPrec i str = first parseOther <$> readsPrec i str

instance (Read l) => Read (RFormula All l) where
    readsPrec i str = first parseAll <$> readsPrec i str

instance (Read l) => Read (RFormula Any l) where
    readsPrec i str = first parseAny <$> readsPrec i str

instance (Read l) => Read (RFormula Odd l) where
    readsPrec i str = first parseOdd <$> readsPrec i str

parseAll :: Read l => Printer -> RFormula All l
parseAll (Roundup "ALL" l) = RAll $ fromList $ do
    e <- l
    return $ case e of
        n@(Roundup "ANY" _) -> Bla $ parseAny n
        n@(Roundup "ODD" _) -> Bla $ parseOdd n
        n                   -> Bla $ parseOther n

parseAny :: Read l => Printer -> RFormula Any l
parseAny (Roundup "ANY" l) = RAny $ fromList $ do
    e <- l
    return $ case e of
        n@(Roundup "ALL" _) -> Bla $ parseAll n
        n@(Roundup "ODD" _) -> Bla $ parseOdd n
        n                   -> Bla $ parseOther n

parseOdd :: Read l => Printer -> RFormula Odd l
parseOdd (Roundup "ODD" l) = ROdd $ fromList $ do
    e <- l
    return $ case e of
        n@(Roundup "ALL" _) -> Bla $ parseAll n
        n@(Roundup "ANY" _) -> Bla $ parseAny n
        n                   -> Bla $ parseOther n

parseOther :: Read l => Printer -> RFormula Other l
parseOther (Terminal s) = RLit $ read s




{-

data Tag = L | A | B | C

data Tree (a :: Tag) v where
    Leaf :: l -> Tree L v
    N1 :: [Bla A v] -> Tree A v
    N2 :: [Bla B v] -> Tree B v
    N3 :: [Bla C v] -> Tree C v

data Bla (x :: Tag) v = forall a. NotEqual a x => Bla (Tree a v)

data General v = forall a. Tree a v

type family NotEqual (a :: Tag) (b :: Tag) :: Constraint where
  NotEqual x x = TypeError (Text "forbidden case")
  NotEqual _ _ = ()

-}

--tester = N1 [Bla (N2 [Bla (N1 []), Bla (N2 [])])]
--tester :: Bla A Int
--tester = Bla (Leaf 5)

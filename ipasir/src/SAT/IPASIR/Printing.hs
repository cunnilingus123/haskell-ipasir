module SAT.IPASIR.Printing where

import Data.List (intercalate)
import Data.Bifunctor (first)

tabsize :: Int
tabsize = 4

data Printer
    = Terminal String
    | Negation Printer
    | Roundup String [Printer]

instance Show Printer where
    show (Terminal s)  = s
    show (Negation s)  = '-' : show s
    show (Roundup s l)
        | any isRoundup l  = s ++ "\n" 
                             ++ symboltab '[' ++ intercalate "\n,   " innerStrings 
                             ++ "\n]"
        | otherwise        = s ++ " " ++ show l
        where
            innerStrings = fmap tabdeeper . show =<< l
            tab          = replicate tabsize ' '
            symboltab x  = x : tail tab
            isRoundup :: Printer -> Bool
            isRoundup (Terminal _) = False
            isRoundup (Negation p) = isRoundup p
            isRoundup _            = True
            tabdeeper :: Char -> String
            tabdeeper '\n' = '\n' : tab
            tabdeeper c    = pure c

instance Read Printer where
    readsPrec i str = do
        (x,xs) <- lex str -- x is "-" in case of a negation.
        let (c, rest) = break (`elem` "[,]") str
        let c' = unwords $ words c -- Multi whitespaces are removed.
        case (x, rest) of
            ("-",  _) -> first Negation     <$> readsPrec i xs
            (_,'[':_) -> first (Roundup c') <$> readsPrec i rest
            _         -> [(Terminal c', rest)]


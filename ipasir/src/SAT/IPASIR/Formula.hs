{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module SAT.IPASIR.Formula where
  {-  ( Formula
    , RFormula
    , DFormula
    , Normal
    , Reduced
    , Demorganed
    , Upper
    , GeneralFormula (..)
    , unpackVar
    , isVar
    , isTerminal
    , asLVar
    , asLit
    , var
    , (&&*)
    , (||*)
    , (++*)
    , (->*)
    , (<->*)
    , FormulaOperation (..)
    , Trans
    , addDefinition
    , freshLit
    , addClause
    , addClauses
    , runTrans
    , runTransComplete
    , formulaToNormalform
    , normalformToCNF
    , formulaToCNF
    , normalformToFormula
    , partitionAll
    , partitionAny
    , partitionOdd
    , lit2ELit
    , transCnf
    , transLit
    , litOfNormalForm
    , litOfAnd
    , litOfOr
    , litOfXor
    ) -}   

import Data.Maybe (fromMaybe)
import Data.List (partition, uncons)
import Data.Map (Map, filterWithKey, mapKeys, (!?))
import Data.String (IsString(..))
import Data.Bifunctor (Bifunctor(..))
import Data.Either (isRight)

import Control.Monad (ap, join)
import Control.Monad.Trans.State.Lazy (State, get, modify, runState)

import SAT.IPASIR.Literals (Literal(Variable, HelperVariable, isPositive, unsign), Lit(..), lit, neg)
import SAT.IPASIR.LBool (LBool(..), lnot, land, lor, lxor)
import SAT.IPASIR.XSAT (XSATLit(..), combineXSATLit, xlitsToClause)
import SAT.IPASIR.ComplexityProblem
import SAT.IPASIR.Printing (Printer(..))

newtype CSATLit v b = CSATLit (Formula v)
    deriving (Show, Eq)

instance Bifunctor CSATLit where
    first  f (CSATLit formula) = CSATLit $ fmap f formula
    second _ (CSATLit formula) = CSATLit formula

instance Ord v => ComplexityProblem (CSATLit v b) where
    type Solution (CSATLit v b) = Map v b

instance Ord v => AssumingProblem (CSATLit v b) where
    type Conflict   (CSATLit v b) = [v]
    type Assumption (CSATLit v b) = Lit v

instance (Ord v) => NPProblem (CSATLit v LBool) where
    checkModel m (CSATLit f) = LTrue == go m f
        where
            go m (Var v)  = fromMaybe LUndef $ m !? v
            go _ No       = LFalse
            go _ Yes      = LTrue
            go m (Not f) = lnot $ go m f
            go m (All l) = foldl land LTrue  $ map (go m) l
            go m (Any l) = foldl lor  LFalse $ map (go m) l
            go m (Odd l) = foldl lxor LFalse $ map (go m) l

newtype CSatToXSatRed csat = CSatToXSatRed Int

type Var v = Either Int v

instance (Ord v) => Reduction (CSatToXSatRed (CSATLit v b)) where
    type CPFrom (CSatToXSatRed (CSATLit v b)) = CSATLit v b
    type CPTo   (CSatToXSatRed (CSATLit v b)) = XSATLit (Var v) b
    newReduction    = CSatToXSatRed 0
    parseSolution _ = mapKeys (\(Right x) -> x) . filterWithKey (\k _ -> isRight k)
    parseEncoding (CSatToXSatRed i) (CSATLit formula) = (xsat, CSatToXSatRed i')
        where
            (i', xsat) = formulaToXSAT formula i

instance (Ord v) => AReduction (CSatToXSatRed (CSATLit v b)) where
    parseAssumption _ a = pure $ Right <$> a
    parseConflict _     = map (\(Right x) -> x) . filter isRight

-- | A Formula that combines @Normal@, @Reduced@ and @Demorganed@ formulas
data Formula v
    = Var v           -- ^ A variable.
    | No              -- ^ The formula @False@.
    | Yes             -- ^ The formula @True@.
    | Not (Formula v) -- ^ Negation.
    | All [Formula v] -- ^ All are @True@. It realized @and@.
    | Any [Formula v] -- ^ At least one is @True@. It realized @or@.
    | Odd [Formula v] -- ^ An odd number is @True@. It realized @exclusive or@.
    deriving (Eq, Functor, Foldable, Traversable)

isYes :: Formula v -> Bool
isYes Yes = True
isYes _   = False

isNo :: Formula v -> Bool
isNo No = True
isNo _  = False

instance Show v => Show (Formula v) where
    show f = show $ toPrinter f
        where
            toPrinter :: Formula v -> Printer
            toPrinter (Var v)       = Terminal $ show $ show v
            toPrinter Yes           = Terminal "YES"
            toPrinter No            = Terminal "NO"
            toPrinter (All l)       = Roundup "ALL" $ map toPrinter l
            toPrinter (Any l)       = Roundup "ANY" $ map toPrinter l
            toPrinter (Odd l)       = Roundup "ODD" $ map toPrinter l
            toPrinter (Not (Not f)) = toPrinter f
            toPrinter (Not (All l)) = Roundup "NOT ALL"$ map toPrinter l
            toPrinter (Not (Any l)) = Roundup "NONE"   $ map toPrinter l
            toPrinter (Not (Odd l)) = Roundup "EVEN"   $ map toPrinter l
            toPrinter (Not t)       = Negation $ toPrinter t

instance Read v => Read (Formula v) where
    readsPrec i str = first fromPrinter <$> readsPrec i str 
        where
            fromPrinter :: Printer -> Formula v
            fromPrinter (Terminal "YES")      = Yes
            fromPrinter (Terminal "NO")       = No
            fromPrinter (Terminal s)          = Var $ read $ read s
            fromPrinter (Negation p)          = Not $ fromPrinter p
            fromPrinter (Roundup "ALL" l)     = All $ map fromPrinter l
            fromPrinter (Roundup "ANY" l)     = Any $ map fromPrinter l
            fromPrinter (Roundup "ODD" l)     = Odd $ map fromPrinter l
            fromPrinter (Roundup "NOT ALL" l) = Not $ All $ map fromPrinter l
            fromPrinter (Roundup "NONE" l)    = Not $ Any $ map fromPrinter l
            fromPrinter (Roundup "EVEN" l)    = Not $ Odd $ map fromPrinter l


instance Applicative Formula where
    pure  = return
    (<*>) = ap

instance Monad Formula where
    return           = Var
    (>>=) (Var v)  f = f v
    (>>=) (Not v)  f = Not $ v >>= f
    (>>=) (All vs) f = All $ map (>>= f) vs
    (>>=) (Any vs) f = Any $ map (>>= f) vs
    (>>=) (Odd vs) f = Odd $ map (>>= f) vs
    (>>=) Yes      _ = Yes
    (>>=) No       _ = No

-- | For easy @Var@ creation.
instance (IsString v) => IsString (Formula v) where
    fromString = return . fromString

innerFormulas :: Formula v -> [Formula v]
innerFormulas (All l) = l
innerFormulas (Any l) = l
innerFormulas (Odd l) = l

-- | Infix operator for @All@.
(&&*) :: Formula v -> Formula v -> Formula v
l &&* r = All [l,r]

-- | Infix operator for @Any@.
(||*) :: Formula v -> Formula v -> Formula v
l ||* r = Any [l,r]

-- | Infix operator for @Odd@. This operator stands for xor. 
(++*) :: Formula v -> Formula v -> Formula v
l ++* r = Odd [l,r]

-- | Infix operator implication.
(->*)  :: Formula v -> Formula v -> Formula v
a ->* b = Not a ||* b

-- | Infix operator equivalence.
(<->*) :: Formula v -> Formula v -> Formula v
a <->* b = Not $ a ++* b

infixr 5  &&*
infixr 4  ||*
infixr 3  ++*
infixl 2  ->*
infixr 1 <->*

{- |Transforms the formula such that the following properties for every formula @f@ hold. 
   Define @g = simplifyFormula f@ and 

        > unLit (Pos x) = Var x 
        > unLit (Neg x) = Not $ Var x 

   for every @x@. Then the following properties hold:

   1. @unLit =<< simplifyFormula f@ is logicly equivalent to @f@.
   2. @g@ does not contain any 'Not'.
   3. @g@ is 'Yes' or 'No' or does not contain any 'Yes' and 'No'.
   4. If @All l@ is a node in @g@, then @l@ contains at least 2 elements.
   5. If @All l@ is a node in @g@, then @l@ does not contain any 'All'.
   6. 4 and 5 also hold for 'Any' and 'Odd'.
   7. @size(g)@ and the runtime of 'simplifyFormula' are in @O(size(f))@.
-}
simplifyFormula :: forall l. (Literal l) => Formula (Variable l) -> Formula l
simplifyFormula f = rFormula f True
    where
        rFormula :: Formula (Variable l) -> Bool -> Formula l
        rFormula Yes b         = bFormula Yes b
        rFormula No  b         = bFormula No  b
        rFormula (All []) b    = bFormula Yes b
        rFormula (Any []) b    = bFormula No  b
        rFormula (Odd []) b    = bFormula No  b
        rFormula (Var x)  b    = Var $ lit b x
        rFormula (Not x)  b    = rFormula x $ not b
        rFormula (Odd l) False = rFormula (Odd (Yes:l)) True
        rFormula (Odd l) _     = case innerForms of 
            []  -> bFormula Yes signed
            [_] -> head innerForms'
            _   -> flatten (Odd innerForms') True
            where
                (yesses, innerForms) = partition isYes $ filter (not . isNo) $ map simplifyFormula l :: ([Formula l], [Formula l])
                signed = odd $ length yesses
                firstNegated = simplifyFormula $ Not $ join $ fmap unLit $ head innerForms
            --    firstNegated = head' $ filter (`notElem` [Yes, No]) $ simplifyFormula . Not <$> l
            --    head' = fst . fromMaybe (error "MERKWÜRDIG") . uncons
                innerForms'
                    | signed    = firstNegated : tail innerForms
                    | otherwise = innerForms
        rFormula f b
            | any isKiller l = killer
            | otherwise   = case innerLists of
                []  -> rFormula ([] <<$ f) b
                [x] -> x
                _   -> flatten (innerLists <<$ f) b
            where
                l = innerFormulas f
                innerLists = filter (not . isNeutral) $ map (`rFormula` b) l
                (isNeutral, isKiller, killer) = case f of
                    (All _) -> (isYes, isNo, No)
                    (Any _) -> (isNo, isYes, Yes)
    --                (Odd _) -> (isNo, const False, undefined)

        (<<$) :: [Formula w] -> Formula u -> Formula w
        x <<$ (All _) = All x
        x <<$ (Any _) = Any x
        x <<$ (Odd _) = Odd x

        flatten :: Formula w -> Bool -> Formula w
        flatten outer b = newL <<$ x
            where
                newL = others ++ concatMap innerFormulas sames
                (sames, others) = partition (same x) $ innerFormulas outer
                x = bFormula outer b
                same (All _) (All _) = True
                same (Any _) (Any _) = True
                same (Odd _) (Odd _) = True
                same _       _       = False
        
        bFormula :: Formula w -> Bool -> Formula w
        bFormula Yes     False = No
        bFormula No      False = Yes
        bFormula (All l) False = Any l
        bFormula (Any l) False = All l
        bFormula x       True  = x

-- | Used in 'formulaToXSAT'.
type Parser v b a = State (Int, XSATLit (Var v) b) a

-- | Reduces a 'Formula' to an equivalent 'XSATLit'-Problem.
--   This algorithm can create helper variables for subformulas. 
--   The helper starts from @Left i@, where @i@ is the second argument.
--   The first component of the resulting tuple is the successor of 
--   the highest used helper variable (or @i@ if no helper were used).
formulaToXSAT :: (Literal l) => Formula (Variable l) -> Int -> (Int, XSATLit (HelperVariable l) b)
formulaToXSAT f i = case f' of
    Yes -> (i, XSATLit [  ]  [])
    No  -> (i, XSATLit [[]] [])
    _   -> (i', combineXSATLit xsat xsat')
    where
        f' = simplifyFormula f
        (xsat, (i',xsat')) = runState (transCnf f') (i, XSATLit [] [])
        
        transCnf :: Formula (Lit v) -> Parser v b (XSATLit (Var v) b)
        transCnf (Var v) = return $ XSATLit [[Right <$> v]] []
        transCnf (All l) = foldl1 combineXSATLit <$> mapM transCnf l
        transCnf (Any l) = do
            helpers <- mapM transLit l
            return $ XSATLit [helpers] []
        transCnf (Odd l) = do
            helpers <- mapM transLit l
            return $ XSATLit [] [xlitsToClause helpers]
        
        transLit :: Formula (Lit v) -> Parser v b (Lit (Var v))
        transLit f = do
            XSATLit cnf xnf <- transCnf f
            orHelper  <- mapM litOfOr cnf
            xorHelper <- mapM litOfXor xnf
            litOfAnd $ orHelper ++ xorHelper

        litOfAnd :: [Lit (Var v)] -> Parser v b (Lit (Var v))
        litOfAnd [l] = return l
        litOfAnd ds = do
            -- Define x <-> d1 ∧ ... ∧ dn
            x <- freshLit
            addXSAT $ (`XSATLit` []) $ (Pos x : [neg d | d <- ds]) : [[Neg x, d] | d <- ds ]
            return $ Pos x

        litOfOr :: [Lit (Var v)] -> Parser v b (Lit (Var v))
        litOfOr [l] = return l
        litOfOr ds = do
            -- Define x <-> d1 ∨ ... ∨ dn
            x <- freshLit            
            addXSAT $ (`XSATLit` []) $ (Neg x : ds) : [ [Pos x, neg d] | d <- ds]
            return $ Pos x

        litOfXor :: Lit [Var v] -> Parser v b (Lit (Var v))
        litOfXor (Pos [l]) = return $ Pos l
        litOfXor (Neg [l]) = return $ Neg l
        litOfXor ds = do
            -- Define z <-> x1 ⊕ ... ⊕ xn 
            z <- freshLit
            addXSAT $ XSATLit [] [neg (fmap (z :) ds)]
            return $ Pos z

        -- Creates a new helper variable.
        freshLit :: Parser v b (Var v)
        freshLit = do
            (i, _) <- get
            modify $ first succ
            return $ Left i
        
        addXSAT :: XSATLit (Var v) b -> Parser v b ()
        addXSAT = modify . second . combineXSATLit

unLit :: Literal l => l -> Formula (Variable l)
unLit l
    | isPositive l = Var $ unsign l
    | otherwise    = Not $ Var $ unsign l

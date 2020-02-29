
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{- |This module provides

        1. The definition of propositional formulas (or formula to be short). 
        2. Transformation functions for formulas. You can also transform them into CNF and XCNF.

    Definition of CNF: Every propositional formula of the form 
    $$ \\varphi = \\bigwedge_{i=1}^{n} \\bigvee_{j=1}^{m_i} (\\lnot) x_{i,j} $$

    Definition of XCNF: Every propositional formula of the form 
    $$ \\varphi = cnf \\wedge \\bigwedge_{i=1}^{n} \\left( (\\lnot) \\bigoplus_{j=1}^{m_i} x_{i,j} \\right) $$
    where \\( cnf \\) is a CNF, \\( \\oplus \\) is the exclusive or. 
-}

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
    , partitionSome
    , partitionOdd
    , lit2ELit
    , transCnf
    , transLit
    , litOfNormalForm
    , litOfAnd
    , litOfOr
    , litOfXor
    ) -}   

import Data.Bits (xor)
import Data.Maybe (maybeToList, isJust)
import Data.List (partition)
import Data.String (IsString(..))
import Data.Bifunctor (first, second)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Control.Monad (ap)
import Control.Monad.Trans.State.Lazy (State, get, modify, put, runState)
import Control.Comonad (extract)

import SAT.IPASIR.Literals (Lit(..), isPositive, fromBool, neg)
import SAT.IPASIR.Clauses (Clause(..), NormalForm, CNF, partitionClauses, oddToCNF)
import SAT.IPASIR.VarCache (Cache, cacheState, newHelper, newVar, newVars)

-- | A Formula that combines @Normal@, @Reduced@ and @Demorganed@ formulas
data Formula v
    = Var v            -- ^ A variable.
    | No               -- ^ The formula @False@.
    | Yes              -- ^ The formula @True@.
    | Not  (Formula v) -- ^ Negation.
    | All  [Formula v] -- ^ All are @True@. It realized @and@.
    | Some [Formula v] -- ^ At least one is @True@. It realized @or@.
    | Odd  [Formula v] -- ^ An odd number is @True@. It realized @exclusive or@. 
    deriving (Show, Eq, Functor, Foldable, Traversable)

instance Applicative Formula where
    pure  = return
    (<*>) = ap

instance Monad Formula where
    return            = Var
    (>>=) (Var  v)  f = f v
    (>>=) (Not  v)  f = Not $ v >>= f
    (>>=) (All  vs) f = All  $ map (>>= f) vs
    (>>=) (Some vs) f = Some $ map (>>= f) vs
    (>>=) (Odd  vs) f = Odd  $ map (>>= f) vs
    (>>=) Yes       _ = Yes
    (>>=) No        _ = No

-- | For easy @Var@ creation.
instance (IsString v) => IsString (Formula v) where
    fromString = return . fromString

unpackAllVars :: Formula v -> [v]
unpackAllVars (All  vs) = concatMap unpackAllVars vs
unpackAllVars (Some vs) = concatMap unpackAllVars vs
unpackAllVars (Odd  vs) = concatMap unpackAllVars vs
unpackAllVars (Not  v ) = unpackAllVars v
unpackAllVars f = maybeToList $ unpackVar f

-- | If the formula is a variable its value is returned in a @Just@. Else @Nothing@
unpackVar :: Formula v -> Maybe v
unpackVar (Var  v) = Just v
unpackVar _        = Nothing

-- | Checks if a formula is a variable. This doesn't include @Yes@ or @No@.
isVar :: Formula v -> Bool
isVar = isJust . unpackVar

-- | Checks if a formula is a leaf. This includes variables, @Yes@ and @No@.
isTerminal :: Formula v -> Bool
isTerminal Yes = True
isTerminal No  = True
isTerminal f   = isVar f

-- | Checks if a formula is a leaf. This includes variables, @Yes@ and @No@.
innerFormulas :: Formula v -> [Formula v]
innerFormulas (All l)  = l
innerFormulas (Some l) = l
innerFormulas (Odd l)  = l

-- | Infix operator for @All@.
(&&*) :: Formula v -> Formula v -> Formula v
l &&* r = All [l,r]

-- | Infix operator for @Some@.
(||*) :: Formula v -> Formula v -> Formula v
l ||* r = Some [l,r]

-- | Infix operator for @Odd@. This operator stands for xor. 
(++*) :: Formula v -> Formula v -> Formula v
l ++* r = Odd [l,r]

-- | Infix operator implication.
(->*)  :: Formula v -> Formula v -> Formula v
a  ->* b = Not a ||* b

-- | Infix operator equivalence.
(<->*) :: Formula v -> Formula v -> Formula v
a <->* b = Not $ a ++* b

infixr 5  &&*
infixr 4  ||*
infixr 3  ++*
infixl 2  ->*
infixr 1 <->*

bFormula :: Formula v -> Bool -> Formula v
bFormula Yes False = No
bFormula No  False = Yes
bFormula (All l)  False = Some l
bFormula (Some l) False = All l
bFormula (Odd l)  False = error "Das hab ich noch nicht gemacht " -- TODO muss ich noch machen
bFormula x        True  = x

flatten :: Formula v -> Bool -> Formula v
flatten outer b = newL <$ x
    where
        newL = others ++ concatMap innerFormulas sames
        (sames, others) = partition (same x) $ innerFormulas outer
        x = bFormula outer b
        same (All _)  (All _)  = True
        same (Some _) (Some _) = True
        same (Odd _)  (Odd _)  = True
        same _        _        = False
        x <$ (All  _) = All x
        x <$ (Some _) = Some x
        x <$ (Odd  _) = Odd x

{- |

-}

rFormula :: Eq v => Formula v -> Bool -> Formula (Lit v)
rFormula (All  [])  b = bFormula Yes b
rFormula (Some [])  b = bFormula Yes b
rFormula (Odd  [])  b = bFormula Yes b
rFormula (All  [x]) b = rFormula x b
rFormula (Some [x]) b = rFormula x b
rFormula (Odd  [x]) b = rFormula x b
rFormula (Var  x) True = Var (Pos x)
rFormula (Var  x) _    = Var (Neg x)
rFormula (Not  x) b  = rFormula x $ not b
rFormula (Odd  x) b = error "Odds hab ich noch nicht geschrieben"
rFormula f b
    | killer `elem` innerLists = killer
    | otherwise                = t
    where
        l = innerFormulas f
        innerLists = filter (/=neutral) $ map (`rFormula` b) l
        t = flatten (All innerLists) b
        neutral  = rFormula $ [] <$ f       -- either Yes or No
        killer   = rFormula $ Not $ neutral -- either Yes or No


{-}


-- | Defines for the different formula steps ('Formula','RFormula','DFormula')
--   some general operations.
class (Foldable (GeneralFormula s), Traversable (GeneralFormula s)) 
      => FormulaOperation s where
    -- | create a var
    makeVar :: v -> GeneralFormula s v
    -- | Removes all occurances of @Yes@ and @No@ from the Formulas.
    rFormula :: GeneralFormula s v -> RFormula v
    -- | Push all occurances of @Not@ down to the variables.
    demorgan :: GeneralFormula s v -> DFormula v
    -- | Negates a formula.
    notB :: GeneralFormula s v -> GeneralFormula s v

instance FormulaOperation Normal where
    makeVar = Var
    rFormula formula
        | isYes reduced  = All []
        | isNo  reduced  = Some []
        | otherwise      = transformer reduced
        where
            isYes Yes = True
            isYes _   = False
            isNo No   = True
            isNo _    = False

            reduced = rFormula' formula

            transformer :: Formula v -> RFormula v
            transformer (Var x)  = Var x
            transformer (Not x)  = Not $ transformer x
            transformer (All l)  = All $ map transformer l
            transformer (Some l) = Some $ map transformer l
            transformer (Odd l)  = Odd $ map transformer l

            rFormula' :: Formula v -> Formula v
            rFormula' (All l)
                | any isNo newForms  = No
                | null reducedList   = Yes
                | otherwise          = All reducedList
                where 
                    newForms         = map rFormula' l
                    reducedList      = filter (not . isYes) newForms
            rFormula' (Some l)
                | any isYes newForms = Yes
                | null reducedList   = No
                | otherwise          = Some reducedList
                where 
                    newForms         = map rFormula' l
                    reducedList      = filter (not . isNo) newForms
            rFormula' (Odd l)
                | null reducedList   = if positive then Yes else No
                | positive           = Odd $ notB (head reducedList) : tail reducedList
                | otherwise          = Odd reducedList
                where 
                    newForms            = map rFormula' l
                    (trash,reducedList) = partition isTerminal newForms
                    positive            = odd $ length $ filter (isYes . rFormula') trash
                    isTerminal form = isNo form' || isYes form'
                        where form' = rFormula' form
            rFormula' (Not x)
                | isYes x' = No
                | isNo x'  = Yes
                | otherwise = Not x'
                where x' = rFormula' x
            rFormula' x = x
    demorgan = demorgan . rFormula
    notB (Not x) = x
    notB f       = Not f

instance FormulaOperation Reduced where
    makeVar = Var
    rFormula = id
    demorgan = pdemorgan
        where
            pdemorgan :: RFormula v -> DFormula v
            pdemorgan (Var x)  = PVar x
            pdemorgan (Not f)  = ndemorgan f
            pdemorgan (All f)  = All  $ map pdemorgan f
            pdemorgan (Some f) = Some $ map pdemorgan f
            pdemorgan (Odd f)  = Odd  $ map pdemorgan f
            ndemorgan :: RFormula v -> DFormula v
            ndemorgan (Var x)  = NVar x
            ndemorgan (Not f)  = pdemorgan f
            ndemorgan (All f)  = Some $ map ndemorgan f
            ndemorgan (Some f) = All  $ map ndemorgan f
            ndemorgan (Odd (x:xs)) = Odd $ map pdemorgan $ notB x : xs
    notB (Not x) = x
    notB f       = Not f

instance FormulaOperation Demorganed where
    makeVar = PVar
    rFormula (PVar x) = Var x
    rFormula (NVar x) = Not $ Var x
    rFormula (All  l) = All  $ map rFormula l
    rFormula (Some l) = Some $ map rFormula l
    rFormula (Odd  l) = Odd  $ map rFormula l
    demorgan = id
    notB     = demorgan . notB . rFormula

{- | Transformation monad. It is used to transform a 'DFormula' info a XCNF. See 
     also @transCnf@. The tupel in the State stands for

        1. The 'Cache'. It is used while transforming to create helper variables
        2. Already generated xclauses. 
-}
type Trans e t v w a = State (Cache e t v w, [Clause w]) a

-- | Return a fresh Lit. The Literal is a new helper variables created 
--   by the 'VarCache' inside of the transformator monad
freshLit :: Trans e t v w (Lit w)
freshLit = do 
    (newVar, newCache) <- newHelper . fst <$> get
    modify $ first $ const newCache
    return $ Pos newVar

-- | Adds one clause into the transformator monad.
addClause :: Clause w -> Trans e t v w ()
addClause clause = addClauses [clause]

-- | Adds some clauses into the transformator monad.
addClauses :: [Clause w] -> Trans e t v w ()
addClauses clauses = modify $ second (clauses++)

v2w :: v -> Trans e t v w w
v2w v = do
    (cache, clauses) <- get
    let (w,cache') = newVar v cache
    put (cache', clauses)
    pure w

-- | Generates the XCNF. The 'VarCache' is used to create helper variables. 
runTrans :: Cache e t v w -> Trans e t v w [Clause w] -> ((e,t), NormalForm w)
runTrans cache trans = (cacheState newCache, (or,xor))
    where
        (mainCNF, (newCache, cnfs) ) = runState trans (cache, [])
        cnf      = mainCNF ++ cnfs
        (or,xor) = partitionClauses True cnf

{-
{- |See also 'runTrans'. The return values stands for

        1. The main XCNF. It is not defining the helper variables in the solver, but uses them. 
        2. The new 'VarCache' (after creating the helper variables).
        3. The XCNF which defines the helper variables.
        4. The definitions of the new helper variables.

    The concatenation of 1 and 3 results in the same NormalForm as by using runTrans that means:

    > snd (runTrans cache t) == let (main,_,rest,_) 
            = runTransComplete cache t in partitionClauses True (main++rest)
-}
runTransComplete :: VarCache v 
                 -> Trans v [Clause (Var v)] 
                 -> ([Clause (Var v)], VarCache v, [Clause (Var v)], [(Var v, DFormula (Var v))])
runTransComplete cache trans = (mainCNF, newCache, cnfs, defs)
    where
        (mainCNF, (newCache, cnfs, defs) ) = runState trans (cache, [], [])
-}

-- -----------------------------------------------------------------------------

-- | Transforms a formula into a XCNF. The 'VarCache' is used to create helper variables.
formulaToNormalform :: (Ord v, FormulaOperation s) 
                    => Cache e t v w -> GeneralFormula s v -> ((e,t), NormalForm w)
formulaToNormalform cache form =  runTrans cache' $ transCnf $ demorgan form
    where
        cache' = snd $ (`newVars` cache) $ Set.toList $ Set.fromList $ unpackAllVars form

-- | Transforms a XCNF into a CNF. That means this function removes all xclauses. 
normalformToCNF :: NormalForm w -> CNF w
normalformToCNF (or,xor) = or ++ concatMap oddToCNF xor

-- | Transforms a formula into a CNF. The 'VarCache' is used to create helper variables. 
formulaToCNF :: (Ord v, FormulaOperation s) 
              => Cache e t v w -> GeneralFormula s v -> ((e,t), CNF w)
formulaToCNF cache formula = second normalformToCNF $ formulaToNormalform cache formula

{- | Transforms a Normalform into a Formula. The resulting formula consists of 
     one 'All', which has only 'Some' and 'Odd' inside (for every clause and xclauses). 
     If you want to transform a cnf into a formula, use 

     > formula = normalformToFormula (cnf,[])

     This function is not the inverse function of 'formulaToNormalform'. Even the type is 
     switching, because the resulting formula has helper variables, so its 
     @Formula (Var v)@ instead of @Formula v@.
-}
normalformToFormula :: forall v. NormalForm v -> Formula v
normalformToFormula (or,xor) = All $ orFormulas ++ xorFormulas
    where
        orFormulas  :: [Formula v]
        orFormulas   = [ Some $ map (transformLitOdd . (Var <$>)) clause | clause <-  or]
        xorFormulas :: [Formula v]
        xorFormulas  = [ transformLitOdd $ Odd . map Var <$> clause | clause <- xor]
        transformLitOdd :: Lit (Formula a) -> Formula a
        transformLitOdd (Pos form) = form
        transformLitOdd (Neg form) = Not form

-- |Just used to implement 'partitionAll', 'partitionSome' and 'partitionOdd'.
partitionList :: (DFormula v -> (Bool,[DFormula v])) -> [DFormula v] -> ([Lit v], [DFormula v])
partitionList f [] = ([],[])
partitionList f (x:xs)
    | isVar x      = (lit x:lits2, rest2)
    | correctType  = (lits1++lits2, rest1++rest2) 
    | otherwise    = (lits2, x:rest2) 
    where
        lit :: DFormula v -> Lit v
        lit (PVar v) = Pos v
        lit (NVar v) = Neg v
        (correctType,list)  = f x
        (lits1, rest1)      = partitionList f list
        (lits2, rest2)      = partitionList f xs

{- |Unpacks recursivly all @All@'s in the list and gives all literals (first returned value)
    and other formulas (second returned value).

    First value: Returns all the literals, which can be reached by only unpacking @All@. It does
    not unpack @Some@ or @Odd@. 

    Second value: Every formula, which also can be reached by unpacking every @All@, but which
    aren't literals

    Example: Denote @a,...,i@ are literals. Then

    > All [
    >     a,
    >     Some [ b, All [c,d] ],
    >     All [e, All [f,g], Odd [h, i]]
    >   ]
    
    would return 
    
    > ( [a,e,f,g], [ Some [b, All [c,d]], Odd [h, i] )
-}
partitionAll  :: [DFormula v] -> ([Lit v], [DFormula v])
partitionAll  = partitionList checker
    where
        checker (All l)  = (True,l)
        checker _        = (False,[])

{- |Equivalent function to 'partitionAll', but unpacking every @Some@ -}
partitionSome :: [DFormula v] -> ([Lit v], [DFormula v])
partitionSome = partitionList checker
    where
        checker (Some l) = (True,l)
        checker _        = (False,[])

{- |Equivalent function to 'partitionAll', but unpacking every @Odd@ -}
partitionOdd :: [DFormula v] -> ([Lit v], [DFormula v])
partitionOdd = partitionList checker
    where
        checker (Odd l)  = (True,l)
        checker _        = (False,[])

-- _____________________________________________________________

-- | Transforms a literal into an ELit (with same value and same sign).
lit2ELit :: Lit v -> Trans e t v w (Lit w)
lit2ELit (Pos x) = Pos <$> v2w x
lit2ELit (Neg x) = Neg <$> v2w x

{- | Return a XCNF which is equivalent to the given formula. Note, that the XCNF 
     also uses helper variables, which are defined in the state of the transformator.
-}

transCnf :: forall e t v w. DFormula v -> Trans e t v w [Clause w]
transCnf (PVar v) = (\w -> [Or [Pos w]]) <$> v2w v
transCnf (NVar v) = (\w -> [Or [Pos w]]) <$> v2w v

transCnf (All l) = do
    a <- mapM transCnf l 
    return $ concat a

transCnf (Some l) = do
    let (lits, complexStuff) = partitionSome l
    helpers <- mapM transLit complexStuff
    lits'   <- mapM lit2ELit lits
    return [Or $ lits' ++ helpers]

transCnf (Odd l) = do
    let (lits, complexStuff) = partitionOdd l
    helpers <- mapM transLit complexStuff
    lits'   <- mapM lit2ELit lits
    let s     = foldl xor True $ map (not . isPositive) $ lits' ++ helpers
    return [XOr $ const (map extract lits') <$> fromBool s]

{- |Returns a variable, which is equivalent to:

    /The given formula is @True@. /

    See 'litOfNormalForm', 'litOfAnd', 'litOfOr' and 'litOfXor' to get more Information about 
    the exact formula.
-}
transLit :: DFormula v -> Trans e t v w (Lit w) 
transLit a = do
    cnf <- transCnf a
    litOfNormalForm cnf

{- |Returns a variable, which is equivalent to:

    /The given XCNF is @True@. /

    See 'litOfAnd', 'litOfOr' and 'litOfXor' to get more Information about the exact formula.
-}
litOfNormalForm :: [Clause w] -> Trans e t v w (Lit w)
litOfNormalForm clauses = do
    let (ors, xors) = partitionClauses False clauses
    orHelper  <- mapM litOfOr ors
    xorHelper <- mapM litOfXor xors
    litOfAnd $ orHelper ++ xorHelper

{- |Returns a variable, which is equivalent to:

    /All literals of the given list are @True@./ 

    If the list of literals has a length of 2 or greater, the function does it by the definition:    
 
    $$ z \\leftrightarrow x_1 \\vee \\ldots \\vee x_n $$

    which can be produced by the formula:

    $$ \\left(z \\vee \\bigvee_{i=1}^n \\lnot x_i\\right) \\wedge 
       \\bigwedge_{i=1}^n \\left( \\lnot  z \\vee x_i \\right)   $$

    In Haskell:

    > All [ 
    >       Some [notB z, x1), 
    >       ...
    >       Some [notB z, xn),
    >       Some [z, notB x1, ... , notB xn]
    >   ]

    The function changes the State of the transformator to add @z@ and its definition 
    to the helper variables.
-}
litOfAnd :: [Lit w] -> Trans e t v w (Lit w)
litOfAnd [l] = return l
litOfAnd ds = do
    x <- freshLit
    -- Define x <-> c1 ∧ ... ∧ cn    
    addClauses [ Or [neg x, c] | c <- ds ]
    addClause $ Or $ x : [neg c | c <- ds]
    return x

{- |Returns a variable, which is equivalent to:

    /One literal of the given list is @True@./ 

    If the list of literals has a length of 2 or greater, the function does it by the definition:    
 
    $$ z \\leftrightarrow x_1 \\vee \\ldots \\vee x_n $$

    which can be produced by the formula:

    $$ \\left(\\lnot z \\vee \\bigvee_{i=1}^n x_i\\right) \\wedge \\bigwedge_{i=1}^n 
       \\left( z \\vee \\lnot x_i \\right)   $$

    In Haskell:

    > All [ 
    >       Some [z, notB x1), 
    >       ...
    >       Some [z, notB xn),
    >       Some [notB z, x1, ... , xn]
    >   ]

    The function changes the State of the transformator to add @z@ and its definition 
    to the helper variables.
-}
litOfOr :: [Lit w] -> Trans e t v w (Lit w)
litOfOr [l] = return l
litOfOr ds = do
    x <- freshLit
    -- Define x <-> d1 ∨ ... ∨ dn
    addClauses [ Or [x, neg d] | d <- ds]
    addClause $ Or $ neg x : ds
    return x

{- |Returns a variable, which is equivalent to:

    /An odd number of literals in the given list are @True@./ 

    If the list of literals has a length of 2 or greater, the 
    function does it by the definition:    
 
    $$ z \\leftrightarrow x_1 \\oplus \\ldots \\oplus x_n $$

    which can be produced by the formula:

    $$ \\lnot z \\oplus x_1 \\oplus \\ldots \\oplus x_n $$

    In Haskell:

    > Odd [ notB z, x1, ..., xn ]

    The function changes the State of the transformator to add @z@ and its definition 
    to the helper variables.
-}
litOfXor :: Lit [w] -> Trans e t v w (Lit w)
litOfXor (Pos [l]) = return $ Pos l
litOfXor (Neg [l]) = return $ Neg l
litOfXor ds = do
    z <- freshLit
    let defForPring = case ds of
            (Pos l)      -> map Pos l
            (Neg (x:xs)) -> Neg x : map Pos xs
    -- Define z <-> x1 ⊕ ... ⊕ xn 
    addClause $ XOr $ neg $ (extract z:) <$> ds
    return z

-}

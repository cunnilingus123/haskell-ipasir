{-# LANGUAGE ScopedTypeVariables #-}

module SAT.IPASIR.VarCache where

import Data.Map (Map, empty, insert, member)
import Data.Bifunctor (first)

import Control.Monad.Trans.State.Lazy

-- type CacheState e t = (e, t)
type Var v = Either Int v

data Cache e t v w = Cache 
    { cacheState   :: (e,t)
    , newHelperGen :: (e,t) -> (w,(e,t))
    , addVar       :: v -> (e,t) -> (w,(e,t))
    }

type IntCache e = Cache e () e e
type VarCache v = Cache Int (Map (Var v) Int) v (Var v) 

newIntCache :: forall e. Enum e => e -> IntCache e
newIntCache starter = Cache (starter, ()) newVar (,)
    where
        newVar :: (e,()) -> (e,(e,()))
        newVar (i,_) = (i, (succ i,()) ) 

newVarCache ::forall v. Ord v => VarCache v
newVarCache = Cache (0, empty) newVar insertVar
    where
        newVar :: (Int, Map (Var v) Int) -> (Var v, (Int, Map (Var v) Int))
        newVar (i, m) = (Left i, (succ i, insert (Left i) i m))
        insertVar :: v -> (Int, Map (Var v) Int) -> (Var v, (Int, Map (Var v) Int))
        insertVar v (i, m) 
            | member v' m = (v',(i, m))
            | otherwise   = (v', (succ i, insert v' i m))
            where
                v' = Right v

newHelper :: Cache e t v w -> (w ,Cache e t v w)
newHelper cache = (w,cache {cacheState = s} )
    where
        (w,s) = newHelperGen cache (cacheState cache)

newVar :: v -> Cache e t v w -> (w ,Cache e t v w)
newVar v cache = (w,cache {cacheState = s} )
    where
        (w,s) =  addVar cache v (cacheState cache)

newVars :: [v] -> Cache e t v w -> ([w] ,Cache e t v w)
newVars l cache = (w,cache { cacheState = s })
    where
        (w,s) = runState sta $ cacheState cache
        sta   = mapM (state . addVar cache) l

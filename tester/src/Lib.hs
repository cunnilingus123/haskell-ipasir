module Lib
    ( module Export
    , someFunc
    , tester
    ) where

import SAT.PseudoBoolean as Export
import Debug.Trace

someFunc :: IO ()
someFunc = putStrLn "someFunc"


tester = evalEncoder defaultConfig [1 $-$ 1, 2 $-$ 2, 3 $-$ 3, 4 $-$ 2] 3 5 $ do 
    c <- getClauses
    traceM $ show c 
    c <- aboveLimited
    traceM $ show c
    c <- encodeNewLeq 2
    traceM $ show c
    return ()
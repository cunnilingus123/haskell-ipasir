module Lib
    ( module Export
    , someFunc
    , tester
    ) where

import SAT.PseudoBoolean as Export
import Debug.Trace

someFunc :: IO ()
someFunc = putStrLn "someFunc"

tester = evalEncoder defaultConfig 10 $ do
    cons <- encodeLeq [1 $-$ 1, 2 $-$ 2, 3 $-$ 3, 4 $-$ 2] 3
    getClauses

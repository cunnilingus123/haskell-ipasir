module SAT.IPASIR.Foldable where

foldl2D :: (Foldable t1, Foldable t2) => (b -> a -> b) -> b -> t1 (t2 a) -> b
foldl2D f = foldl $ foldl f

foldr2D :: (Foldable t1, Foldable t2) => (a -> b -> b) -> b -> t1 (t2 a) -> b
foldr2D f = foldr $ flip $ foldr f
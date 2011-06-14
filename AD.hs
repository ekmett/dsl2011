module AD where

data Dual a = Dual { primal :: a, deriv :: a } deriving (Show)




instance Eq a => Eq (Dual a) where
  Dual a _ == Dual b _ = a == b

instance (Ord a, Num a) => Num (Dual a) where
  Dual a b + Dual c d = Dual (a + c) (b + d)
  Dual a b * Dual c d = Dual (a * c) (a*d + b*c)
  Dual a b - Dual c d = Dual (a - c) (b - d)
  negate (Dual a b) = Dual (negate a) (negate b)
  abs (Dual a b) | a <= 0    = negate (Dual a b)
                 | otherwise = Dual a b
  signum (Dual a b) = Dual (signum a) 0
  fromInteger n = Dual (fromInteger n) 0 

lift :: Num a => a -> Dual a 
lift a = Dual a 0

epsilon :: Num a => Dual a
epsilon = Dual 0 1

d :: (Num a, Ord a) => (Dual a -> Dual a) -> a -> a
d f a = case f (Dual a 1) of
    Dual y y' -> y'

d2 :: (Num a, Ord a) => (Dual a -> Dual a -> Dual a) -> a -> a -> (a, a)
d2 f a b = 

    let Dual y dyda = f (lift a + epsilon) (lift b)
        Dual y dydb = f (lift a) (lift b + epsilon)
    in (dyda, dydb)


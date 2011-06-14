{-# LANGUAGE Rank2Types, DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleInstances #-}
module TrainTrack where

import Data.Traversable
import Data.Foldable hiding (sum)
import Numeric.AD

data Cline a = Cline { p, a, b, k :: a } deriving (Read,Show,Functor,Foldable,Traversable)

class (Ord t, Floating t) => ClineType t where
  liftCline :: Cline Double -> Cline t
  liftK :: Double -> t
  
instance ClineType Double where
  liftCline = id
  liftK = id
  
instance Mode s => ClineType (AD s Double) where
  liftCline (Cline p a b k) = Cline (lift p) (lift a) (lift b) (lift k)
  liftK = lift

type Known = Double
type Unknown s = AD s Double

anticlockwise_circle :: Double -> Double -> Double -> Cline Double
anticlockwise_circle x y r = Cline 1 x y (x^2 + y^2 - r^2)

clockwise_circle :: Double -> Double -> Double -> Cline Double
clockwise_circle x y r = Cline (-1) (-x) (-y) (r^2 - x^2 - y^2)

line :: Double -> Double -> Cline Double
line d theta = Cline 0 (-(sin theta)) (cos theta) (2 * d)

point :: Double -> Double -> Cline Double
point x y = Cline 1 x y 0 

type Constraints s = [AD s Double]

reverse_cline :: ClineType a => Cline a -> Cline a 
reverse_cline (Cline p a b k) = Cline (-p) (-a) (-b) (-k)

passing_through :: Mode s => Double -> Double -> Cline (Unknown s) -> Constraints s
passing_through x y (Cline p a b k) = 
  [(x^2 + y^2) *^ p - (2 * x) *^ a - (2 * y) *^ b + k]

anticlockwise_radius :: Mode s => Double -> Cline (Unknown s) -> Constraints s
anticlockwise_radius r (Cline p a b k) = [r *^ p - sqrt (a^2 + b^2 - k*p)]

clockwise_radius :: Mode s => Double -> Cline (Unknown s) -> Constraints s
clockwise_radius r (Cline p a b k) = [r *^ p + sqrt (a^2 + b^2 - k*p)]

concentric_with :: Mode s => Cline Double -> Cline (Unknown s) -> Constraints s
concentric_with (Cline p1 a1 b1 k1) (Cline p2 a2 b2 k2) = 
  [ (a1^2 + b1^2) *^ p2 - p1 *^ (a1 *^ a2 + b1 *^ b2)
  , (p1^2 + b1^2) *^ a2 - a1 *^ (p1 *^ p2 + b1 *^ b2)
  , (p1^2 + a1^2) *^ b2 - b1 *^ (p1 *^ p2 + a1 *^ a2)
  ]

centered_at :: Mode s => Double -> Double -> Cline (Unknown s) -> Constraints s
centered_at x y = concentric_with (point x y)
  
crossing_angle :: Mode s => Double -> Cline Double -> Cline (Unknown s) -> Constraints s
crossing_angle theta (Cline p1 a1 b1 k1) (Cline p2 a2 b2 k2) = 
  [ k1 *^ p2 + p1 *^ k2 - (2 * a1) *^ a2 - (2 * b1) *^ b2 + (2 * cos theta * sqrt1) *^ sqrt2 ] where
  sqrt1 = sqrt (a1^2 + b1^2 - k1*p1)
  sqrt2 = sqrt (a2^2 + b2^2 - k2*p2)

tangent_to :: Mode s => Cline Double -> Cline (Unknown s) -> Constraints s  
tangent_to = crossing_angle 0

offset_cline :: ClineType a => Double -> Cline a -> Cline a 
offset_cline d (Cline p a b k) = Cline p a b k'
  where
    d' = liftK d
    k' = k - 2 * d' * sqrt (a^2 + b^2 - k*p) - p*d'^2

near_manhole :: Mode s => Double -> Double -> Double -> Cline (Unknown s) -> Constraints s
near_manhole x y d = passing_through x y . offset_cline d

is_line :: Mode s => Cline (Unknown s)  -> Constraints s
is_line (Cline p a b k) = [p]

satisfying :: Mode s => [Cline (Unknown s) -> Constraints s] -> Cline (Unknown s) -> Constraints s
satisfying cs c = cs >>= ($c)

data C a = C a a a deriving (Functor, Foldable, Traversable)

cline :: ClineType t => Cline Double -> C t -> Cline t
cline base (C p' a' b') = Cline p' a' b' k' where 
  Cline p a b k = liftCline base
  x = (p' - p) * (p' + p) + (a' - a) * (a' + a) + (b' - b) * (b' + b)
  k' | k < 0     = k + x
     | otherwise = k - x

find :: Cline Double -> (forall s. Mode s => Cline (Unknown s) -> Constraints s) -> Cline Double
find c@(Cline p a b k) constraints = cline c $ optimize (sum . map (^2) . constraints . cline c) (C p a b)

steps = 50

optimize :: Traversable f => (forall s. Mode s => f (Unknown s) -> Unknown s) -> f Double -> f Double
optimize f guess = gradientDescent f guess `near` steps where
  near [] _ = guess
  near [x] n = x
  near (x:xs) 0 = x
  near (x:xs) n = near xs $! (n - 1)

{-
cline1 :: Cline Double
cline1 = find guess1 $ satisfying
  [ passing_through x1 y1
  , passing_through x2 y2
  , clockwise_radius r
  ]

cline2 :: Cline Double
cline2 = find guess2 $ satisfying
  [ tangent_to cline1
  , passing_through x y
  , is_line
  ]

[cline1', cline2'] = map (offset_cline 3.405) [cline1, cline2]
-}


{-
foo = find estimate $ satisfying [
   passing_through x y
   tangent_to c1
   tangent_to c2
 ]
-}

-- data Shape a = Line a a a  -- a*x + b*y + k = 0
--             | Circle a a a -- x^2 + y^2 - 2ax-2by + k = 0 -- a circle centered at a,b with radius k

-- clineToShape :: Eq a => Cline a -> Shape a
-- clineToShape (Cline 0 a b k) = Line (-2*a) (-2*b) k
-- clineToShape (Cline p a b k) = Circle (a / p) (b / p) ((a/p)^2 + (b/p)^2)

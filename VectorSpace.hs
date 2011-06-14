{-# LANGUAGE TypeFamilies, FlexibleContexts, TypeOperators, UndecidableInstances, RankNTypes, ScopedTypeVariables #-}
module VectorSpace where

import Data.Functor.Representable.Trie hiding (Entry)
import Data.Key (Adjustable(..), Key)
import qualified Data.Key as Key
import qualified Data.Heap as Heap
import Data.Heap (Heap, Entry(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty(..))
import Data.Complex hiding (phase)
import Prelude hiding (flip)
import Data.List (foldl')
import qualified Data.Map as Map
import Control.Applicative
import Control.Monad
import Control.Monad.Free
import Control.Monad.Codensity
import Control.Monad.Trans

infixl 6 .*, ./

class (Alternative v, MonadPlus v, Num (Scalar v)) => Vector v where
  type Scalar v :: *
  (.*) :: Scalar v -> v a -> v a

  linear :: (forall u. (Vector u, Scalar u ~ Scalar v) => [(Scalar v, u a)]) -> v a
  linear xs = foldr (\(p,va) b -> p .* va <|> b) empty xs

  linear_ :: [(Scalar v, a)] -> v a
  linear_ as = linear [ (p,pure a) | (p,a) <- as ]

(./) :: (Vector v, Fractional (Scalar v)) => v a -> Scalar v -> v a 
v ./ s = recip s .* v

flip :: Vector v => Scalar v -> v Bool
flip p = linear_ [(p,True),(1-p,False)]

instance Vector v => Vector (Free v) where
  type Scalar (Free v) = Scalar v
  p .* Free as = Free (p .* as)
  p .* v = Free $ linear_ [(p,v)]
  linear xs = Free $ linear_ xs

instance Vector v => Vector (Codensity v) where
  type Scalar (Codensity v) = Scalar v
  p .* Codensity m = Codensity (\k -> p .* m k)
  linear xs = lift $ linear xs
  linear_ = lift . linear_ 

class Vector v => Eval v where
  eval :: Ord a => v a -> [(Scalar v,a)]
  flatten :: v a -> [(Scalar v, a)]

instance Eval v => Eval (Free v) where
  eval    = eval . retract
  flatten = flatten . retract

{-
instance Eval v => Eval (Codensity v) where
  eval = eval . lowerCodensity
  flatten = flatten . lowerCodensity
-}

optimize :: (Eval v, Ord a) => v a -> v a
optimize = linear_ . eval

-- | conservative upper bound on the L1 norm. Accurate If all vectors are non-negative.
d :: Eval v => v a -> Scalar v
d = foldl' (\b pa -> b + abs (fst pa)) 0 . flatten

newtype Linear p a = Linear { runLinear :: [(p,a)] } 
  deriving (Read,Show)

instance Num p => Functor (Linear p) where
  fmap f (Linear as) = Linear [ (p, f a) | (p,a) <- as ]
  b <$ as = Linear [(d as, b)]

instance Num p => Applicative (Linear p) where
  pure a = Linear [(1, a)]
  Linear fs <*> Linear as = Linear [(p*q,f a) | (p,f) <- fs, (q,a) <- as]
  as <* bs = d bs .* as
  as *> bs = d as .* bs
  
instance Num p => Alternative (Linear p) where
  empty = Linear []
  Linear as <|> Linear bs = Linear (as <|> bs)

instance Num p => Monad (Linear p) where
  return a = Linear [(1, a)]
  (>>) = (*>)
  Linear as >>= f = Linear [ (p*q, b) | (p,a) <- as, (q,b) <- runLinear (f a) ]

instance Num p => MonadPlus (Linear p) where
  mzero = empty
  mplus = (<|>)

instance Num p => Vector (Linear p) where
  type Scalar (Linear p) = p
  p .* Linear as = Linear [ (p*q,a) | (q,a) <- as ]
  linear_ = Linear

instance Num p => Eval (Linear p) where
  eval = map swap . Map.toList . Map.fromListWith (+) . map swap . runLinear
    where 
      swap :: (a,b) -> (b,a)
      swap (a,b) = (b,a)
  flatten = runLinear

pl :: Linear Double a -> Linear Double a
pl = id

pf :: Free (Linear Double) a -> Free (Linear Double) a
pf = id

pc :: Codensity (Free (Linear Double)) a -> Codensity (Free (Linear Double)) a
pc = id

ql :: Linear (Complex Double) a -> Linear (Complex Double) a
ql = id

qf :: Free (Linear (Complex Double)) a -> Free (Linear (Complex Double)) a
qf = id

qc :: Codensity (Free (Linear (Complex Double))) a -> Codensity (Free (Linear (Complex Double))) a
qc = id

grassModel :: (Vector v, Fractional (Scalar v)) => v Bool
grassModel = do
  cloudy    <- flip 0.5
  rain      <- flip $ if cloudy then 0.8 else 0.2
  sprinkler <- flip $ if cloudy then 0.1 else 0.5
  _wetRoof  <- (&& rain) <$> flip 0.7
  wetGrass  <- (||) <$> ((&&) rain <$> flip 0.9)
                    <*> ((&&) sprinkler <$> flip 0.9)
  cup True wetGrass -- guard wetGrass
  return rain


class Ord a => Space a where
  cup :: Vector v => a -> a -> v ()
  cap :: Vector v => v (a,a)

instance Space () where
  cup () () = pure ()
  cap = pure ((),())

instance Space Bool where
  cup True True = pure ()
  cup False False = pure ()
  cup _ _ = empty
  cap = pure (True, True) <|> pure (False,False)

instance (Space a, Space b) => Space (a, b) where
  cup (a,b) (a',b') = do
    cup a a'
    cup b b'
  cap = abide <$> cap <*> cap
    where abide (a,b) (c,d) = ((a,c),(b,d))

instance (Space a, Space b) => Space (Either a b) where
  cup (Left a) (Left b) = cup a b
  cup (Right a) (Right b) = cup a b
  cup _ _ = empty
  cap = fmap (\(a,b) -> (Left a, Left b)) cap <|> fmap (\(a,b) -> (Right a, Right b)) cap

transpose :: (Vector v, Space a, Space b) => (a -> v b) -> b -> v a
transpose m i = do
  (k,l) <- cap
  j <- m k
  cup i j
  return l

-- False plays the role of |0>
-- True plays the role of |1>
-- a|0> + b|1> where |a|^2 + |b|^2 = 1

-- rotate by a unitary matrix
rot :: Vector v => Scalar v -> Scalar v -> Scalar v -> Scalar v -> Bool -> v Bool
rot f t _ _ False = linear_ [(f,False), (t, True)]
rot _ _ f t True  = linear_ [(f,False), (t, True)]

hadamard :: (Vector v, Floating (Scalar v)) => Bool -> v Bool
hadamard = rot h h 
               h (-h) 
 where h = recip (sqrt 2)


xor :: Bool -> Bool -> Bool
xor True True = False
xor True False = True
xor False True = True
xor False False = False

pauliX :: Applicative v => Bool -> v Bool
pauliX = pure . not

pauliY :: (Vector v, Scalar v ~ Complex r, RealFloat r) => Bool -> v Bool
pauliY = rot 0 (-i)
             i 0 where i = 0 :+ 1

pauliZ :: Vector v => Bool -> v Bool
pauliZ = rot 1 0 
             0 (-1)

phase :: (Vector v, Scalar v ~ Complex r, RealFloat r) => Bool -> v Bool
phase = rot 1 0 
            0 i where i = 0 :+ 1

pi_8 :: (Vector v, Scalar v ~ Complex r, RealFloat r) => Bool -> v Bool
pi_8 = rot 1 0
           0 (cis (pi/4))

swap :: Applicative v => Bool -> Bool -> v (Bool, Bool)
swap a b = pure (b, a)

controlled :: Applicative v => (a -> v a) -> Bool -> a -> v a
controlled m a b = if a then m b else pure b

controlledZ :: Vector v => Bool -> Bool -> v Bool
controlledZ = controlled pauliZ

controlledNot :: Applicative v => Bool -> Bool -> v Bool
controlledNot = controlled (pure . not)

controlledPhase :: (Vector v, Scalar v ~ Complex r, RealFloat r) => Bool -> Bool -> v Bool
controlledPhase = controlled phase 

qplus, qminus :: (Vector v, Scalar v ~ Complex r, RealFloat r) => v Bool
qplus = hadamard False
qminus = hadamard True

qphase :: (Vector v, Scalar v ~ Complex r, RealFloat r) => r -> Bool -> v Bool
qphase  phi = rot 1 0 
                  0 c 
  where c = cis $ 2 * pi * phi

condense :: Int -> NonEmpty a -> NonEmpty a
condense n (a:|as0) | n >= 1 = go a as0 n
  where
    go a []     _ = a :| []
    go a (b:bs) 1 = a :| NonEmpty.toList (go b bs n)
    go _ (b:bs) k = go b bs $! (k - 1)

newtype Reverse a = Reverse a

instance Eq a => Eq (Reverse a) where
  Reverse a == Reverse b = a == b

instance Ord a => Ord (Reverse a) where
  compare (Reverse a) (Reverse b) = compare b a

buildHeap :: (Eval v, Ord p) => (Scalar v -> p) -> Scalar v -> v (Free v a) -> (Heap (Entry (Reverse p) (Scalar v, Free v a)), p)
buildHeap f q = convert . foldr act ([],0) . flatten where
      act (p,a) (xs,sz) = (x:xs, qp+sz) where 
          qp = q*p
          x = Entry (Reverse (f qp)) (qp,a)
      convert (xs,sz) = (Heap.fromList xs, f sz) 

-- used when we need no priority

data Trivial = Trivial deriving (Eq,Ord,Show)

instance Num Trivial where
  _ + _ = Trivial
  _ * _ = Trivial
  _ - _ = Trivial
  abs _ = Trivial
  signum _ = Trivial
  fromInteger _ = Trivial

-- always expands the tree in the direction that maximizes information.
-- returns a list of lower bounds on the proability with one sided error
proj_ :: (Eval v, Num p, Ord p) => (Scalar v -> p) -> Free v a -> NonEmpty (Scalar v, p)
proj_ f (Pure b)  = (1, f 0) :| []
proj_ f (Free bs) = condense 20 $ go 0 ub0 entries0
    where 
        (entries0, ub0) = buildHeap f 1 bs 
        go lo err heap = (lo,err) :| case Heap.viewMin heap of 
            Nothing -> []
            Just (Entry (Reverse q) (p, Pure c), heap') -> NonEmpty.toList $ go (lo + p) (err - q) heap'
            Just (Entry (Reverse q) (p, Free cs), heap') -> let (heap'', q) = buildHeap f p cs in NonEmpty.toList $ 
                go lo (err - f p + q) $ Heap.union heap' heap''

-- always expands the tree in the direction that maximizes information. Only yields valid Improving values when the 
-- probabilities always correctly lie within the interval 0..1
proj :: (Eval v, Num p, Ord p, Eq a, HasTrie a) => (Scalar v -> p) -> Free v a -> NonEmpty (a :->: Scalar v, p)
proj f (Pure b) = (adjust (const 1) b (pure 0), f 0) :| []
proj f (Free bs) = condense 20 $ go (pure 0) ub0 entries0
    where 
        (entries0, ub0) = buildHeap f 1 bs 
        go lo err heap = (lo,err) :| case Heap.viewMin heap of 
            Nothing -> []
            Just (Entry (Reverse q) (p, Pure c), heap') -> NonEmpty.toList $ go (adjust (+ p) c lo) (err - q) heap'
            Just (Entry (Reverse q) (p, Free cs), heap') -> let (heap'', q) = buildHeap f p cs in NonEmpty.toList $ 
                go lo (err - f p + q) $ Heap.union heap' heap''

-- run a quantum computation, extracting classical bits
measure :: (Vector v, Eval u, Scalar u ~ Complex r, RealFloat r, Fractional (Scalar v), Ord a) => u a -> v a
measure qbits = linear_ [ (fromRational $ toRational $ magnitude q ^ 2, a) | (q,a) <- eval qbits ]

drunken :: (Vector v, Fractional (Scalar v)) => Int -> Int -> Int -> Int -> v Bool
drunken _ l _ y | y >= l          = pure True
drunken w _ x _ | x <= 0 || x > w = pure False
drunken w l x y = linear [(0.25, drunken w l x       y)
                         ,(0.25, drunken w l (x - 1) y)
                         ,(0.25, drunken w l (x + 1) y)
                         ,(0.25, drunken w l x (y + 1))]

{-# LANGUAGE KindSignatures
           , TypeFamilies
           , MultiParamTypeClasses
           , NoMonomorphismRestriction
           , GADTs
           , FlexibleInstances #-}
module QM where

class IxMonad m where
  ireturn :: a -> m i i a 
  (>>>=) :: m i j a -> (a -> m j k b) -> m i k b

newtype An a = An a 
data    Used = Used

class QSymantics repr where
  bool   :: Num p => Bool -> repr p h h Bool
  int    :: Num p => Int -> repr p h h Int
  add    :: Num p => repr p hi h Int -> repr p h ho Int -> repr p hi ho Int
  rot    :: Num p => p -> p -> p -> p -> repr p hi ho Bool -> repr p hi ho Bool
  app    :: Num p => repr p hi h (a -> b) -> repr p h ho a -> repr p hi ho b
  s      :: Num p => repr p hi ho a -> repr p (any,hi) (any, ho) a 
  z      :: Num p => repr p (An a, h) (Used, h) a
  linear :: Num p => [(p, repr p hi ho a)] -> repr p hi ho a 

hadamard = rot h h h (-h) where h = recip (sqrt 2)

qplus, qminus :: (QSymantics repr, Floating p) => repr p h h Bool
qplus = hadamard (bool True)
qminus = hadamard (bool False)
  
class LinearL repr hi ho where
  lam :: Num p => repr p (An a, hi) (Used, ho) b -> repr p hi ho (a -> b)

-- t11 :: QSymantics repr => repr hi hi p Int
t11 = add (int 1) (int 2)

newtype R p hi ho a = R { runR :: hi -> [(p, a, ho)] }

instance Functor (R p hi ho) where 
  fmap f e = R $ \hi -> [(p,f a,ho) | (p, a, ho) <- runR e hi ]

instance Num p => Monad (R p hi hi) where
  return = ireturn
  (>>=) = (>>>=)

instance Num p => IxMonad (R p) where
  ireturn a = R $ \hi -> [(1,a,hi)]
  e >>>= f = R $ \hi -> do
    (p,a,h)  <- runR e hi
    (q,b,ho) <- runR (f a) h
    return (p*q,b,ho)
  
liftIx2 :: IxMonad m => (a -> b -> c) -> m i j a -> m j k b -> m i k c
liftIx2 f ma mb = ma >>>= \a -> mb >>>= \b -> ireturn (f a b)

instance QSymantics R where
  bool = return
  int = return
  add = liftIx2 (+)
  -- linear :: [(p, repr p hi ho a)] -> repr p hi ho a 
  linear ps = R $ \hi -> do
    (p,r) <- ps
    (q,a,ho) <- runR r hi
    [(p*q,a,ho)]
  rot pa pb pc pd e1 = R $ \hi -> do
    (p,bit,ho) <- runR e1 hi
    if not bit then [(p*pa,False,ho),(p*pb,True,ho)]
               else [(p*pc,False,ho),(p*pd,True,ho)]
  z = R $ \(An a,h) -> [(1,a,(Used,h))]
  s v = R $ \(any,hi) -> do 
    (p,x,ho) <- runR v hi
    [(p,x,(any,ho))]
  app = liftIx2 id

class HiHo hi ho where
    hiho :: hi -> ho

instance HiHo () () where
    hiho = id

instance HiHo hi ho => HiHo (An a,hi) (An a,ho) where
    hiho (x,hi) = (x, hiho hi)

instance HiHo hi ho => HiHo (An a,hi) (Used,ho) where
    hiho (x,hi) = (Used, hiho hi)

data F p hi ho a where
  Pure :: a -> F p hi hi a 
  Free :: R p hi h (F p h ho a) -> F p hi ho a

-- instance HiHo hi ho => LinearL F hi ho where
--   lam :: Num p => F p (An a, hi) (Used, ho) b -> F p hi ho (a -> b)

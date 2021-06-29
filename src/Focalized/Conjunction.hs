module Focalized.Conjunction
( -- * Conjunction
  Conj(..)
, exlrC
, curryConj
, uncurryConj
, foldMapConj
, traverseConj
, bifoldMapConj
, bimapConj
, bitraverseConj
) where

-- Conjunction

import Control.Applicative (liftA2)

class Conj c where
  (-><-) :: a -> b -> (a `c` b)
  infix 4 -><-
  exl :: (a `c` b) -> a
  exr :: (a `c` b) -> b

instance Conj (,) where
  (-><-) = (,)
  exl = fst
  exr = snd

exlrC :: Conj c => (a' -> b' -> r) -> (a -> a') -> (b -> b') -> (a `c` b -> r)
exlrC h f g = h <$> f . exl <*> g . exr

curryConj :: Conj p => ((a `p` b) -> r) -> (a -> b -> r)
curryConj f = fmap f . (-><-)

uncurryConj :: Conj p => (a -> b -> r) -> ((a `p` b) -> r)
uncurryConj f = exlrC f id id

foldMapConj :: Conj p => (b -> m) -> (a `p` b) -> m
foldMapConj f = f . exr

traverseConj :: (Conj p, Applicative m) => (b -> m b') -> (a `p` b) -> m (a `p` b')
traverseConj = exlrC (liftA2 (-><-)) pure

bifoldMapConj :: (Conj p, Monoid m) => (a -> m) -> (b -> m) -> (a `p` b -> m)
bifoldMapConj = exlrC (<>)

bimapConj :: Conj p => (a -> a') -> (b -> b') -> (a `p` b -> a' `p` b')
bimapConj = exlrC (-><-)

bitraverseConj :: (Conj p, Applicative m) => (a -> m a') -> (b -> m b') -> (a `p` b -> m (a' `p` b'))
bitraverseConj = exlrC (liftA2 (-><-))

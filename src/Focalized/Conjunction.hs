module Focalized.Conjunction
( -- * Conjunction
  Conj(..)
, (-><-)
, curryConj
, uncurryConj
, foldMapConj
, traverseConj
, bifoldMapConj
, bimapConj
, bitraverseConj
) where

-- Conjunction

class Conj c where
  inlr :: a -> b -> (a `c` b)
  exl :: (a `c` b) -> a
  exr :: (a `c` b) -> b

instance Conj (,) where
  inlr = (,)
  exl = fst
  exr = snd

(-><-) :: Conj c => a -> b -> (a `c` b)
(-><-) = inlr

infix 4 -><-

curryConj :: Conj p => ((a `p` b) -> r) -> (a -> b -> r)
curryConj f = fmap f . inlr

uncurryConj :: Conj p => (a -> b -> r) -> ((a `p` b) -> r)
uncurryConj f = f <$> exl <*> exr

foldMapConj :: Conj p => (b -> m) -> (a `p` b) -> m
foldMapConj f = f . exr

traverseConj :: (Conj p, Applicative m) => (b -> m b') -> (a `p` b) -> m (a `p` b')
traverseConj f c = inlr (exl c) <$> f (exr c)

bifoldMapConj :: (Conj p, Monoid m) => (a -> m) -> (b -> m) -> (a `p` b -> m)
bifoldMapConj f g = (<>) <$> f . exl <*> g . exr

bimapConj :: Conj p => (a -> a') -> (b -> b') -> (a `p` b -> a' `p` b')
bimapConj f g = inlr <$> f . exl <*> g . exr

bitraverseConj :: (Conj p, Applicative m) => (a -> m a') -> (b -> m b') -> (a `p` b -> m (a' `p` b'))
bitraverseConj f g c = inlr <$> f (exl c) <*> g (exr c)

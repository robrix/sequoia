module Sequoia.Conjunction
( -- * Conjunction
  Conj(..)
, (~><~)
, _exl
, _exr
, exlrC
, curryConj
, uncurryConj
, foldMapConj
, traverseConj
, bifoldMapConj
, bimapConj
, bitraverseConj
  -- * Lifted projections
, exlK
, exrK
, exlF
, exrF
, exlL
, exrL
, exlR
, exrR
) where

-- Conjunction

import Control.Applicative (liftA2)
import Data.Functor.Contravariant
import Data.Profunctor
import Sequoia.Bijection

class Conj c where
  (-><-) :: a -> b -> (a `c` b)
  infix 4 -><-
  exl :: (a `c` b) -> a
  exr :: (a `c` b) -> b

instance Conj (,) where
  (-><-) = (,)
  exl = fst
  exr = snd

(~><~) :: Conj c => (s -> a) -> (s -> b) -> (s -> (a `c` b))
(l ~><~ r) s = l s -><- r s

infix 4 ~><~

_exl :: Conj c => Optic Lens (a `c` b) (a' `c` b) a a'
_exl = lens exl (\ c -> (-><- exr c))

_exr :: Conj c => Optic Lens (a `c` b) (a `c` b') b b'
_exr = lens exr (\ c -> (exl c -><-))

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


-- Lifted projections

exlK :: (Contravariant k, Conj c) => k a -> k (a `c` b)
exrK :: (Contravariant k, Conj c) => k b -> k (a `c` b)
exlK = contramap exl
exrK = contramap exr

exlF :: (Functor f, Conj c) => f (a `c` b) -> f a
exrF :: (Functor f, Conj c) => f (a `c` b) -> f b
exlF = fmap exl
exrF = fmap exr

exlL :: (Profunctor p, Conj c) => p a r -> p (a `c` b) r
exrL :: (Profunctor p, Conj c) => p b r -> p (a `c` b) r
exlL = lmap exl
exrL = lmap exr

exlR :: (Profunctor p, Conj c) => p l (a `c` b) -> p l a
exrR :: (Profunctor p, Conj c) => p l (a `c` b) -> p l b
exlR = rmap exl
exrR = rmap exr

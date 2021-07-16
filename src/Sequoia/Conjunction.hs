module Sequoia.Conjunction
( -- * Conjunction
  Conj(..)
, inlr
, _exl
, _exr
, exlrC
  -- * Generalizations
, coerceConj
, swapConj
, curryConj
, uncurryConj
, firstConj
, secondConj
  -- * Defaults
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
  (>--<) :: (s -> a) -> (s -> b) -> (s -> a `c` b)
  infix 4 >--<
  exl :: (a `c` b) -> a
  exr :: (a `c` b) -> b

instance Conj (,) where
  (>--<) = liftA2 (,)
  exl = fst
  exr = snd

inlr :: Conj c => a -> b -> a `c` b
inlr a b = (const a >--< const b) ()

_exl :: Conj c => Optic Lens (a `c` b) (a' `c` b) a a'
_exl = lens exl (\ c -> (`inlr` exr c))

_exr :: Conj c => Optic Lens (a `c` b) (a `c` b') b b'
_exr = lens exr (\ c -> (exl c `inlr`))

exlrC :: Conj c => (a' -> b' -> r) -> (a -> a') -> (b -> b') -> (a `c` b -> r)
exlrC h f g = h <$> f . exl <*> g . exr


-- Generalizations

coerceConj :: (Conj c1, Conj c2) => a `c1` b -> a `c2` b
coerceConj = exl >--< exr

swapConj :: Conj c => a `c` b -> b `c` a
swapConj = exr >--< exl

curryConj :: Conj p => (a `p` b -> r) -> (a -> b -> r)
curryConj f = fmap f . inlr

uncurryConj :: Conj p => (a -> b -> r) -> (a `p` b -> r)
uncurryConj f = exlrC f id id

firstConj :: (Conj c, Strong p) => p a b -> p (c a d) (c b d)
firstConj = dimap coerceConj coerceConj . first'

secondConj :: (Conj c, Strong p) => p a b -> p (c d a) (c d b)
secondConj = dimap coerceConj coerceConj . second'


-- Defaults

foldMapConj :: Conj p => (b -> m) -> (a `p` b -> m)
foldMapConj f = f . exr

traverseConj :: (Conj p, Applicative m) => (b -> m b') -> (a `p` b) -> m (a `p` b')
traverseConj = exlrC (liftA2 inlr) pure

bifoldMapConj :: (Conj p, Monoid m) => (a -> m) -> (b -> m) -> (a `p` b -> m)
bifoldMapConj = exlrC (<>)

bimapConj :: Conj p => (a -> a') -> (b -> b') -> (a `p` b -> a' `p` b')
bimapConj = exlrC inlr

bitraverseConj :: (Conj p, Applicative m) => (a -> m a') -> (b -> m b') -> (a `p` b -> m (a' `p` b'))
bitraverseConj = exlrC (liftA2 inlr)


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

module Sequoia.Conjunction
( -- * Conjunction
  Conj(..)
, inlr
, _exl
, _exr
, _exlA
, _exrA
, exlrC
, (>∘∘<)
, assocL
, assocR
, assocConj
, distConjRep
, undistConjF
  -- * Generalizations
, coerceConj
, swapConj
, curryConj
, uncurryConj
, firstConj
, secondConj
, (***)
, (&&&)
, dupConj
, unfirstConj
, unsecondConj
, lensConj
  -- * Defaults
, foldMapConj
, fmapConj
, traverseConj
, bifoldMapConj
, bimapConj
, bitraverseConj
, bisequenceConj
, bidistributeConj
  -- * Lifted projections
, exlK
, exrK
, exlF
, exrF
, exlL
, exrL
, exlR
, exrR
  -- * Optics
, coercedConj
, bimappingConj
, firstingConj
, secondingConj
) where

-- Conjunction

import Control.Applicative (liftA2)
import Control.Category (Category, (>>>))
import Data.Functor.Contravariant
import Data.Functor.Rep as Co
import Data.Profunctor
import Fresnel.Iso
import Fresnel.Lens
import Sequoia.Bifunctor.Product
import Sequoia.Profunctor.Diagonal
import Sequoia.Profunctor.Value

class Conj c where
  {-# MINIMAL exl, exr, ((>--<) | (>---<)) #-}

  (>--<) :: a -> b -> a `c` b
  a >--< b = (const a >---< const b) ()
  infix 4 >--<

  (>---<) :: (s -> a) -> (s -> b) -> (s -> a `c` b)
  (>---<) = liftA2 (>--<)

  infix 4 >---<

  exl :: (a `c` b) -> a
  exr :: (a `c` b) -> b

instance Conj (,) where
  (>--<) = (,)
  exl = fst
  exr = snd

instance Conj (×) where
  a >--< b = P (\ k -> k a b)
  exl = exPl
  exr = exPr


inlr :: Conj c => a -> b -> a `c` b
inlr = (>--<)

_exl :: Conj c => Lens (a `c` b) (a' `c` b) a a'
_exl = lens exl (\ c -> (>--< exr c))

_exr :: Conj c => Lens (a `c` b) (a `c` b') b b'
_exr = lens exr (\ c -> (exl c >--<))

_exlA :: (Conj c, Applicative f) => Lens (f (a `c` b)) (f (a' `c` b)) (f a) (f a')
_exlA = lens exlF (liftA2 (flip (>--<)) . exrF)

_exrA :: (Conj c, Applicative f) => Lens (f (a `c` b)) (f (a `c` b')) (f b) (f b')
_exrA = lens exrF (liftA2 (>--<) . exlF)

exlrC :: Conj c => (a' -> b' -> r) -> (a -> a') -> (b -> b') -> (a `c` b -> r)
exlrC h f g = h <$> f . exl <*> g . exr


(>∘∘<) :: Conj d => e ∘ b -> e ∘ c -> e ∘ (b `d` c)
V a >∘∘< V b = V (a >---< b)

infix 3 >∘∘<


assocL :: Conj p => a `p` (b `p` c) -> (a `p` b) `p` c
assocL = (exl &&& exl . exr) &&& exr . exr

assocR :: Conj p => (a `p` b) `p` c -> a `p` (b `p` c)
assocR = exl . exl &&& exr . exl &&& exr

assocConj :: (Conj p, Conj q) => Iso
  (a `p` (b `p` c)) (a' `q` (b' `q` c'))
  ((a `p` b) `p` c) ((a' `q` b') `q` c')
assocConj = iso assocL assocR


distConjRep :: (Co.Representable f, Conj c1, Conj c2) => (f a `c1` f b) -> f (a `c2` b)
distConjRep = uncurryConj (\ a b -> tabulate (\ c -> index a c >--< index b c))

undistConjF :: (Functor f, Conj c1, Conj c2) => f (a `c1` b) -> (f a `c2` f b)
undistConjF = fmap exl &&& fmap exr


-- Generalizations

coerceConj :: (Conj c1, Conj c2) => a `c1` b -> a `c2` b
coerceConj = exl >---< exr

swapConj :: Conj c => a `c` b -> b `c` a
swapConj = exr >---< exl

curryConj :: Conj p => (a `p` b -> r) -> (a -> b -> r)
curryConj f = fmap f . inlr

uncurryConj :: Conj p => (a -> b -> r) -> (a `p` b -> r)
uncurryConj f = exlrC f id id

firstConj :: (Conj c, Strong p) => p a b -> p (c a d) (c b d)
firstConj = dimap coerceConj coerceConj . first'

secondConj :: (Conj c, Strong p) => p a b -> p (c d a) (c d b)
secondConj = dimap coerceConj coerceConj . second'

(***) :: (Strong p, Category p, Conj c) => a1 `p` b1 -> a2 `p` b2 -> (a1 `c` a2) `p` (b1 `c` b2)
f *** g = firstConj f >>> secondConj g

infixr 3 ***

(&&&) :: (Strong p, Category p, Conj c, Diagonal p) => a `p` b1 -> a `p` b2 -> a `p` (b1 `c` b2)
f &&& g = dupConj >>> f *** g

infixr 3 &&&

dupConj :: (Diagonal p, Conj c) => a `p` (a `c` a)
dupConj = rmap coerceConj dup

unfirstConj :: (Conj c, Costrong p) => p (c a d) (c b d) -> p a b
unfirstConj = unfirst . dimap coerceConj coerceConj

unsecondConj :: (Conj c, Costrong p) => p (c d a) (c d b) -> p a b
unsecondConj = unsecond . dimap coerceConj coerceConj


lensConj :: Conj c => (s -> a) -> (s `c` b -> t) -> Lens s t a b
lensConj get = lens get . curryConj


-- Defaults

foldMapConj :: Conj p => (b -> m) -> (a `p` b -> m)
foldMapConj f = f . exr

fmapConj :: Conj p => (b -> b') -> (a `p` b -> a `p` b')
fmapConj = exlrC inlr id

traverseConj :: (Conj p, Applicative m) => (b -> m b') -> (a `p` b) -> m (a `p` b')
traverseConj = exlrC (liftA2 inlr) pure

bifoldMapConj :: (Conj p, Monoid m) => (a -> m) -> (b -> m) -> (a `p` b -> m)
bifoldMapConj = exlrC (<>)

bimapConj :: Conj p => (a -> a') -> (b -> b') -> (a `p` b -> a' `p` b')
bimapConj = exlrC inlr

bitraverseConj :: (Conj p, Applicative m) => (a -> m a') -> (b -> m b') -> (a `p` b -> m (a' `p` b'))
bitraverseConj = exlrC (liftA2 inlr)

bisequenceConj :: (Conj p, Applicative f) => f a `p` f b -> f (a `p` b)
bisequenceConj = uncurryConj (liftA2 (>--<))

bidistributeConj :: (Conj c, Functor g) => g (a `c` b) -> g a `c` g b
bidistributeConj = fmap exl >---< fmap exr


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


-- Optics

coercedConj :: (Conj c, Conj d, Conj c', Conj d') => Iso (c a b) (c' a' b') (d a b) (d' a' b')
coercedConj = coerceConj `iso` coerceConj

bimappingConj :: (Conj p, Conj q) => Iso s t a b -> Iso s' t' a' b' -> Iso (p s s') (q t t') (p a a') (q b b')
bimappingConj a b = withIso a $ \ lsa lbt -> withIso b $ \ rsa rbt -> bimapConj lsa rsa `iso` bimapConj lbt rbt

firstingConj :: (Conj p, Conj q) => Iso s t a b -> Iso (p s x) (q t y) (p a x) (q b y)
firstingConj a = withIso a $ \ lsa lbt -> firstConj lsa `iso` firstConj lbt

secondingConj :: (Conj p, Conj q) => Iso s t a b -> Iso (p x s) (q y t) (p x a) (q y b)
secondingConj b = withIso b $ \ rsa rbt -> secondConj rsa `iso` secondConj rbt

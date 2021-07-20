module Sequoia.Profunctor.Coexponential
( -- * Coexponential profunctor
  Coexp(..)
  -- * Construction
, idCoexp
  -- * Elimination
, runCoexp
, withCoexp
  -- * Optics
, recall_
, forget_
) where

import Data.Functor.Contravariant
import Data.Profunctor
import Sequoia.Functor.K
import Sequoia.Functor.V

-- Coexponential profunctor

data Coexp e r a b = Coexp { recall :: V e b, forget :: K r a }
  deriving (Functor)

instance Profunctor (Coexp e r) where
  dimap f g c = Coexp (g <$> recall c) (f >$< forget c)


-- Construction

idCoexp :: Coexp b a a b
idCoexp = Coexp (V id) (K id)


-- Elimination

runCoexp :: Coexp e r b a -> (a -> b) -> (e -> r)
runCoexp (Coexp a b) = (runK b .) . (. runV a)

withCoexp :: Coexp e r b a -> ((e -> a) -> (b -> r) -> s) -> s
withCoexp c f = f (runV (recall c)) (runK (forget c))


-- Optics

type Lens s t a b = (forall p . Strong p => p a b -> p s t)

recall_ :: Lens (Coexp e r a b) (Coexp e' r a b') (V e b) (V e' b')
recall_ = lens recall (\ s recall -> s{ recall })

forget_ :: Lens (Coexp e r a b) (Coexp e r' a' b) (K r a) (K r' a')
forget_ = lens forget (\ s forget -> s{ forget })

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens prj inj = dimap (\ s -> (prj s, s)) (\ (b, s) -> inj s b) . first'

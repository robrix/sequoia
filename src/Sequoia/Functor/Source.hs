module Sequoia.Functor.Source
( -- * Sources
  Src(..)
  -- * Computation
, mapSrcK
, mapSrcV
) where

import Data.Profunctor
import Sequoia.Continuation
import Sequoia.Functor.K
import Sequoia.Functor.V
import Sequoia.Optic.Getter
import Sequoia.Optic.Iso
import Sequoia.Optic.Review
import Sequoia.Profunctor.Context
import Sequoia.Value

-- Sources

newtype Src e r b = Src { runSrc :: K r b -> C e r }

instance Functor (Src e r) where
  fmap f = Src . (. contramap f) . runSrc

instance Applicative (Src e r) where
  pure = Src . fmap res . flip runK
  Src f <*> Src a = Src (\ k -> cont (\ _K -> f (_K (\ f -> a (inK (exK k . f))))))

instance Monad (Src e r) where
  Src m >>= f = Src (\ k -> cont (\ _K -> m (_K ((`runSrc` k) . f))))

instance Env1 Src where
  env1 f = Src (\ k -> env ((`runSrc` k) . f))

instance Res1 Src where
  res1 = Src . const . res
  liftRes1 f = Src (\ k -> liftRes (\ run -> runSrc (f (run . (`runSrc` k))) k))


-- Computation

mapSrcK :: (forall x . K r x <-> K r' x) -> (Src e r b -> Src e r' b)
mapSrcK b = Src . dimap (review b) (mapCK (view b)) . runSrc

mapSrcV :: (forall x . V e x -> V e' x) -> (Src e r b -> Src e' r b)
mapSrcV f = Src . fmap (mapCV f) . runSrc

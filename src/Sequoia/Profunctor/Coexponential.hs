module Sequoia.Profunctor.Coexponential
( -- * Coexponential profunctor
  Coexp(..)
  -- * Construction
, idCoexp
  -- * Elimination
, runCoexp
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

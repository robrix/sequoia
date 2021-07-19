module Sequoia.Profunctor.Coexponential
( -- * Coexponential profunctor
  Coexp(..)
  -- * Construction
, idCoexp
  -- * Elimination
, runCoexp
) where

import Data.Profunctor

-- Coexponential profunctor

data Coexp e r a b = Coexp { recall :: e -> b, forget :: a -> r }
  deriving (Functor)

instance Profunctor (Coexp e r) where
  dimap f g c = Coexp (g . recall c) (forget c . f)


-- Construction

idCoexp :: Coexp b a a b
idCoexp = Coexp id id


-- Elimination

runCoexp :: Coexp e r b a -> (a -> b) -> (e -> r)
runCoexp (Coexp a b) = (b .) . (. a)

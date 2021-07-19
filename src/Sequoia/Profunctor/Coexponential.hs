module Sequoia.Profunctor.Coexponential
( -- * Coexponential profunctor
  Coexp(..)
  -- * Construction
, idCoexp
  -- * Elimination
, runCoexp
) where

-- Coexponential profunctor

data Coexp e r b a = Coexp { coexpA :: e -> a, coexpB :: b -> r }
  deriving (Functor)


-- Construction

idCoexp :: Coexp b a a b
idCoexp = Coexp id id


-- Elimination

runCoexp :: Coexp e r b a -> (a -> b) -> (e -> r)
runCoexp (Coexp a b) = (b .) . (. a)

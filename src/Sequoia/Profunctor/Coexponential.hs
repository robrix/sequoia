module Sequoia.Profunctor.Coexponential
( -- * Coexponential profunctor
  Coexp(..)
  -- * Elimination
, runCoexp
) where

-- Coexponential profunctor

data Coexp e r b a = Coexp { coexpA :: e -> a, coexpB :: b -> r }
  deriving (Functor)


-- Elimination

runCoexp :: Coexp e r b a -> (a -> b) -> (e -> r)
runCoexp (Coexp a b) = (b .) . (. a)

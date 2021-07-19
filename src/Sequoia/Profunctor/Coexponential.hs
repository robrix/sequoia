module Sequoia.Profunctor.Coexponential
( runCoexp
, Coexp(..)
) where

runCoexp :: Coexp e r b a -> (a -> b) -> (e -> r)
runCoexp (Coexp a b) = (b .) . (. a)

data Coexp e r b a = Coexp { coexpA :: e -> a, coexpB :: b -> r }
  deriving (Functor)

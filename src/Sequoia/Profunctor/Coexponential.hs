module Sequoia.Profunctor.Coexponential
( Coexp(..)
) where

data Coexp e r b a = Coexp { coexpA :: e -> a, coexpB :: b -> r }
  deriving (Functor)

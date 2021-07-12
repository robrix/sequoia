module Sequoia.Functor.Applicative
( Contrapplicative(..)
) where

import Data.Functor.Contravariant

class Contravariant k => Contrapplicative k where
  contraliftA2 :: (c -> Either a b) -> k a -> k b -> k c

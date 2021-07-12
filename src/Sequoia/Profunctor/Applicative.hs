module Sequoia.Profunctor.Applicative
( Coapplicative(..)
) where

import Data.Profunctor

class Profunctor p => Coapplicative p where
  coliftA2 :: (c -> Either a b) -> p a z -> p b z -> p c z

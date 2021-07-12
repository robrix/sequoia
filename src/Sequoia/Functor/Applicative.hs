module Sequoia.Functor.Applicative
( Contrapply(..)
, Contrapplicative(..)
) where

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Rep

class Contravariant k => Contrapply k where
  {-# MINIMAL contraliftA2 | contrap #-}

  contraliftA2 :: (c -> Either a b) -> k a -> k b -> k c
  contraliftA2 f a b = contramap f (contrap a b)

  contrap :: k a -> k b -> k (Either a b)
  contrap = contraliftA2 id

  coapl :: k a -> k b -> k a
  coapl = contraliftA2 Left

  coapr :: k a -> k b -> k b
  coapr = contraliftA2 Right

class (Contrapply k, Representable k) => Contrapplicative k where
  contrapure :: (a -> Rep k) -> k a
  contrapure = tabulate

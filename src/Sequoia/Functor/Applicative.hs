{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.Functor.Applicative
( -- * Contravariant applicative
  comap
, Contrapply(..)
, Contrapplicative(..)
) where

import Data.Functor.Contravariant
import Sequoia.Profunctor.Exp

-- Contravariant applicative

comap :: Contravariant f => (a' -> a) -> (f a -> f a')
comap = contramap

class Contravariant f => Contrapply r f | f -> r where
  {-# MINIMAL coliftC2 | (<&>) #-}

  coliftC2 :: ((b >-r-~ c) -> a) -> f a -> f b -> f c
  coliftC2 f = (<&>) . comap f

  (<&>) :: f (a >-r-~ b) -> f a -> f b
  (<&>) = coliftC2 id

  infixl 4 <&>


class Contrapply r f => Contrapplicative r f | f -> r where
  copure :: (b -> a) -> f (a >-r-~ b)

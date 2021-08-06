{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.Functor.Applicative
( -- * Contravariant applicative
  comap
, Contrapply(..)
, Contrapplicative(..)
  -- * Coexponentials
, type (>-)
, type (-~)
) where

import Data.Functor.Contravariant
import Data.Kind (Type)

-- Contravariant applicative

comap :: Contravariant f => (a' -> a) -> (f a -> f a')
comap = contramap

class Contravariant f => Contrapply co f | f -> co where
  {-# MINIMAL coliftC2 | (<&>) #-}

  coliftC2 :: ((b >-co-~ c) -> a) -> f a -> f b -> f c
  coliftC2 f = (<&>) . comap f

  (<&>) :: f (a >-co-~ b) -> f a -> f b
  (<&>) = coliftC2 id

  infixl 4 <&>


class Contrapply co f => Contrapplicative co f | f -> co where
  copure :: (b -> a) -> f (co a b)


-- Coexponentials

type b >-r = (r :: Type -> Type -> Type) b
type r-~ a = r a

infixr 1 >-
infixr 0 -~

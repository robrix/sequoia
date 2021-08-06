{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.Profunctor.Applicative
( Coapply(..)
, Coapplicative(..)
  -- * Coexponentials
, type (>-)
, type (-~)
) where

import Data.Kind (Type)
import Data.Profunctor

class Profunctor p => Coapply co p | p -> co where
  {-# MINIMAL coliftC2 | (<&>) #-}

  coliftC2 :: ((b >-co-~ c) -> a) -> p a d -> p b d -> p c d
  coliftC2 f = (<&>) . lmap f

  (<&>) :: p (a >-co-~ b) d -> p a d -> p b d
  (<&>) = coliftC2 id

  infixl 4 <&>

class Coapply co p => Coapplicative co p | p -> co where
  copure :: (b -> a) -> p (co a b) c


-- Coexponentials

type b >-r = (r :: Type -> Type -> Type) b
type r-~ a = r a

infixr 1 >-
infixr 0 -~

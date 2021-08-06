{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.Profunctor.Applicative
( ProfunctorCPS(..)
, Coapply(..)
, Coapplicative(..)
  -- * Exponentials
, type (~~)
, type (~>)
  -- * Coexponentials
, type (>-)
, type (-~)
) where

import Data.Kind (Type)
import Data.Profunctor

class Profunctor p => ProfunctorCPS ex p | p -> ex where
  lmapCPS :: (a' ~~ex~> a) -> (p a b -> p a' b)
  rmapCPS :: (b ~~ex~> b') -> (p a b -> p a b')

class Profunctor p => Coapply co p | p -> co where
  {-# MINIMAL coliftC2 | (<&>) #-}

  coliftC2 :: ((b >-co-~ c) -> a) -> p a d -> p b d -> p c d
  coliftC2 f = (<&>) . lmap f

  (<&>) :: p (a >-co-~ b) d -> p a d -> p b d
  (<&>) = coliftC2 id

  infixl 3 <&>

class Coapply co p => Coapplicative co p | p -> co where
  copure :: (b -> a) -> p (co a b) c


-- Exponentials

type a ~~r = (r :: Type -> Type -> Type) a
type r~> b = r b

infixr 1 ~~
infixr 0 ~>


-- Coexponentials

type b >-r = (r :: Type -> Type -> Type) b
type r-~ a = r a

infixr 1 >-
infixr 0 -~

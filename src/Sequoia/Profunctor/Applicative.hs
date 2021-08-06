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

import Control.Category as Cat hiding ((.))
import Data.Kind (Type)
import Data.Profunctor

class (Profunctor p, Cat.Category ex) => ProfunctorCPS ex p | p -> ex where
  {-# MINIMAL dimapCPS | (lmapCPS, rmapCPS) #-}

  dimapCPS :: (a' ~~ex~> a) -> (b ~~ex~> b') -> (p a b -> p a' b')
  dimapCPS f g = rmapCPS g . lmapCPS f

  lmapCPS :: (a' ~~ex~> a) -> (p a b -> p a' b)
  lmapCPS = (`dimapCPS` Cat.id)

  rmapCPS :: (b ~~ex~> b') -> (p a b -> p a b')
  rmapCPS = (Cat.id `dimapCPS`)

class Profunctor p => Coapply co p | p -> co where
  {-# MINIMAL coliftC2 | (<&>) #-}

  coliftC2 :: ((b >-co-~ c) -> a) -> p a d -> p b d -> p c d
  coliftC2 f = (<&>) . lmap f

  (<&>) :: p (a >-co-~ b) d -> p a d -> p b d
  (<&>) = coliftC2 Prelude.id

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

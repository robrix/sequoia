{-# LANGUAGE FunctionalDependencies #-}
module Sequoia.Profunctor.Applicative
( ProfunctorCPS(..)
, (<#>)
, Coapply(..)
, Coapplicative(..)
) where

import Control.Category as Cat hiding ((.))
import Data.Profunctor
import Prelude hiding (exp)
import Sequoia.Profunctor.Exp

class Profunctor p => ProfunctorCPS r p | p -> r where
  {-# MINIMAL dimapCPS | (lmapCPS, rmapCPS) #-}

  dimapCPS :: (a' ~~r~> a) -> (b ~~r~> b') -> (p a b -> p a' b')
  dimapCPS f g = rmapCPS g . lmapCPS f

  lmapCPS :: (a' ~~r~> a) -> (p a b -> p a' b)
  lmapCPS = (`dimapCPS` Cat.id)

  rmapCPS :: (b ~~r~> b') -> (p a b -> p a b')
  rmapCPS = (Cat.id `dimapCPS`)

(<#>) :: ProfunctorCPS r p => (c -> Either a b) -> p a d -> p (b >-r-~ c) d
(<#>) = lmapCPS . cocurry . exp'

infixl 3 <#>

class Profunctor p => Coapply r p | p -> r where
  {-# MINIMAL coliftC2 | (<&>) #-}

  coliftC2 :: ((b >-r-~ c) -> a) -> p a d -> p b d -> p c d
  coliftC2 f = (<&>) . lmap f

  (<&>) :: p (a >-r-~ b) d -> p a d -> p b d
  (<&>) = coliftC2 Prelude.id

  infixl 3 <&>

instance Coapply r (Exp r) where
  coliftC2 f (Exp a) (Exp b) = Exp (\ k c -> a k (f (b k :>- c)))
  Exp f <&> Exp a = Exp (\ k b -> f k (a k :>- b))

class Coapply r p => Coapplicative r p | p -> r where
  copure :: (b -> a) -> p (a >-r-~ b) c

instance Coapplicative r (Exp r) where
  copure f = Exp (\ _ (a :>- b) -> a (f b))

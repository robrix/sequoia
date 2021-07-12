module Sequoia.Profunctor.Applicative
( Coapply(..)
, Coapplicative(..)
) where

import Data.Profunctor
import Data.Profunctor.Rep

class Profunctor p => Coapply p where
  {-# MINIMAL coliftA2 | coap #-}

  coliftA2 :: (c -> Either a b) -> p a d -> p b d -> p c d
  coliftA2 f a b = lmap f (coap a b)

  coap :: p a c -> p b c -> p (Either a b) c
  coap = coliftA2 id

  coapl :: p a c -> p b c -> p a c
  coapl = coliftA2 Left

  coapr :: p a c -> p b c -> p b c
  coapr = coliftA2 Right

instance Coapply (->) where
  coliftA2 f a b = either a b . f
  coap = either


class (Representable p, Coapply p) => Coapplicative p where
  copure :: (a -> Rep p b) -> p a b
  copure = tabulate

instance Coapplicative (->)

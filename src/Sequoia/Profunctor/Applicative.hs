module Sequoia.Profunctor.Applicative
( Coapplicative(..)
) where

import Data.Profunctor

class Profunctor p => Coapplicative p where
  {-# MINIMAL coliftA2 | coap #-}

  coliftA2 :: (c -> Either a b) -> p a d -> p b d -> p c d
  coliftA2 f a b = lmap f (coap a b)

  coap :: p a c -> p b c -> p (Either a b) c
  coap = coliftA2 id

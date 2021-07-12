module Sequoia.Profunctor.Applicative
( Coapplicative(..)
) where

import Data.Profunctor

class Profunctor p => Coapplicative p where
  {-# MINIMAL coliftA2 | coap #-}

  coliftA2 :: (c -> Either a b) -> p a z -> p b z -> p c z
  coliftA2 f a b = lmap f (coap a b)

  coap :: p a z -> p b z -> p (Either a b) z
  coap = coliftA2 id

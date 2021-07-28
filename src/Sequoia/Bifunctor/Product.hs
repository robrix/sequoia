module Sequoia.Bifunctor.Product
( -- * Product type
  type (×)(..)
) where

import Data.Bifunctor

-- Product type

newtype a × b = P { getP :: forall t . (a -> b -> t) -> t }
  deriving (Functor)

infixr 7 ×

instance Bifunctor (×) where
  bimap f g (P p) = P (\ lr -> p (\ l r -> lr (f l) (g r)))

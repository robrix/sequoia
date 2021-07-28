module Sequoia.Bifunctor.Product
( -- * Product type
  type (×)(..)
) where

-- Product type

newtype a × b = P { getP :: forall t . (a -> b -> t) -> t }
  deriving (Functor)

infixr 7 ×

module Sequoia.Profunctor.Product
( (:*:)(..)
) where

newtype (p :*: q) a b = Product { runProduct :: (p a b, q a b) }

infixr 6 :*:

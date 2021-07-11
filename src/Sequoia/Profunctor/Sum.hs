module Sequoia.Profunctor.Sum
( (:+:)(..)
) where

newtype (p :+: q) a b = Sum { runSum :: Either (p a b) (q a b) }

infixr 5 :+:

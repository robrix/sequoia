-- | A contravariant functor over a profunctor’s input.
module Sequoia.Functor.In
( In(..)
) where

newtype In p r a = In { runIn :: p a r }

module Sequoia.Functor.V
( V(..)
) where

import Data.Profunctor

newtype V s a = V { runV :: s -> a }
  deriving (Applicative, Choice, Closed, Cochoice, Costrong, Functor, Monad, Monoid, Profunctor, Semigroup, Strong)

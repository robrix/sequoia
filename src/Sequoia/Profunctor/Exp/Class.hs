module Sequoia.Profunctor.Exp.Class
( -- * Exponentials
  Exponential(..)
, exp'
) where

import Data.Profunctor
import Prelude hiding (exp)

-- Exponentials

class Profunctor ex => Exponential ex where
  exp :: ((b -> r) -> (a -> r)) -> ex a b

  app :: ex a b -> ((b -> r) -> (a -> r))

exp' :: Exponential ex => (a -> b) -> ex a b
exp' f = exp (. f)

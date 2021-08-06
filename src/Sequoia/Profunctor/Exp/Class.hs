module Sequoia.Profunctor.Exp.Class
( -- Exponentials
  Exponential(..)
) where

import Data.Profunctor

-- Exponentials

class Profunctor ex => Exponential ex where
  exp :: ((b -> r) -> (a -> r)) -> ex a b

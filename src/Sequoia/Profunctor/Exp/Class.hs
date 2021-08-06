module Sequoia.Profunctor.Exp.Class
( -- Exponentials
  Exponential(..)
) where

import Data.Profunctor

-- Exponentials

class Profunctor ex => Exponential ex where
  exp :: (a -> b) -> ex a b

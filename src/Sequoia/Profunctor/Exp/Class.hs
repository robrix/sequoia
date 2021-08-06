module Sequoia.Profunctor.Exp.Class
( -- * Exponentials
  Exponential(..)
, exp'
  -- * Coexponentials
, Coexponential(..)
  -- * Computation
, cocurry
) where

import Data.Profunctor
import Prelude hiding (exp)

-- Exponentials

class Profunctor ex => Exponential ex where
  exp :: ((b -> r) -> (a -> r)) -> ex a b

  app :: ex a b -> ((b -> r) -> (a -> r))

exp' :: Exponential ex => (a -> b) -> ex a b
exp' f = exp (. f)


-- Coexponentials

class Profunctor co => Coexponential co where
  runCoexp :: ((a -> r) -> (b -> r)) -> (co a b -> r)


-- Computation

cocurry :: (Exponential ex, Coexponential co) => ex c (Either a b) -> ex (co b c) a
cocurry f = exp (\ k -> runCoexp (app f . either k))

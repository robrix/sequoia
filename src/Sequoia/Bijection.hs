module Sequoia.Bijection
( -- * Bijections
  Optic
, Optic'
) where

-- Bijections

type Optic p s t a b = (a `p` b) -> (s `p` t)

type Optic' p s a = (a `p` a) -> (s `p` s)

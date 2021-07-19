module Sequoia.Bijection
( -- * Bijections
  Optic
, Optic'
  -- ** Elimination
, dimap2
) where

-- Bijections

type Optic p s t a b = (a `p` b) -> (s `p` t)

type Optic' p s a = (a `p` a) -> (s `p` s)


-- Elimination

dimap2 :: (a' -> a) -> (b' -> b) -> (c -> c') -> (a -> b -> c) -> (a' -> b' -> c')
dimap2 l1 l2 r f a1 a2 = r (f (l1 a1) (l2 a2))

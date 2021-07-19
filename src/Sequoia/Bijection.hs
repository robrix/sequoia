module Sequoia.Bijection
( -- * Bijections
  Optic
, Optic'
  -- ** Elimination
, over
, dimap2
) where

-- Bijections

type Optic p s t a b = (a `p` b) -> (s `p` t)

type Optic' p s a = (a `p` a) -> (s `p` s)


-- Elimination

over :: Optic (->) s t a b -> (a -> b) -> (s -> t)
over f = f


dimap2 :: (a' -> a) -> (b' -> b) -> (c -> c') -> (a -> b -> c) -> (a' -> b' -> c')
dimap2 l1 l2 r f a1 a2 = r (f (l1 a1) (l2 a2))

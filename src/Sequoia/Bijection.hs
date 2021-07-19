module Sequoia.Bijection
( -- * Bijections
  Optic
, Optic'
  -- ** Elimination
, reviews
, (<~)
, over
, dimap2
) where

import Sequoia.Profunctor.Recall

-- Bijections

type Optic p s t a b = (a `p` b) -> (s `p` t)

type Optic' p s a = (a `p` a) -> (s `p` s)


-- Elimination

reviews :: Optic (Recall e) s t a b -> (e -> b) -> (e -> t)
reviews b = runRecall . b . Recall


(<~) :: Optic (Recall b) s t a b -> (b -> t)
o <~ b = reviews o id b

infixr 8 <~


over :: Optic (->) s t a b -> (a -> b) -> (s -> t)
over f = f


dimap2 :: (a' -> a) -> (b' -> b) -> (c -> c') -> (a -> b -> c) -> (a' -> b' -> c')
dimap2 l1 l2 r f a1 a2 = r (f (l1 a1) (l2 a2))

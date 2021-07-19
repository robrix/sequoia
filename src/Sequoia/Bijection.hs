module Sequoia.Bijection
( -- * Bijections
  Optic
  -- ** Elimination
, views
, reviews
, (<~)
, (~>)
, over
, dimap2
  -- ** Composition
, idB
) where

import Data.Profunctor
import Sequoia.Profunctor.Recall

-- Bijections

type Optic p s t a b = (a `p` b) -> (s `p` t)


-- Elimination

views   :: Optic (Forget r) s t a b -> (a -> r) -> (s -> r)
views   b = runForget . b . Forget

reviews :: Optic (Recall e) s t a b -> (e -> b) -> (e -> t)
reviews b = runRecall . b . Recall


(~>) :: s -> Optic (Forget a) s t a b -> a
s ~> o = views o id s

infixl 8 ~>

(<~) :: Optic (Recall b) s t a b -> (b -> t)
o <~ b = reviews o id b

infixr 8 <~


over :: Optic (->) s t a b -> (a -> b) -> (s -> t)
over f = f


dimap2 :: (a' -> a) -> (b' -> b) -> (c -> c') -> (a -> b -> c) -> (a' -> b' -> c')
dimap2 l1 l2 r f a1 a2 = r (f (l1 a1) (l2 a2))


-- Composition

idB :: Optic p s s s s
idB = id

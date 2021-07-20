module Sequoia.Optic.Review
( -- * Reviews
  Review
, Review'
  -- * Construction
, unto
  -- ** Elimination
, reviews
, review
, (<~)
) where

import Control.Effect.Reader
import Data.Bifunctor
import Data.Profunctor
import Sequoia.Bicontravariant (lphantom)
import Sequoia.Optic.Optic
import Sequoia.Profunctor.Recall

-- Reviews

type Review s t a b = forall p . (Bifunctor p, Profunctor p) => Optic p s t a b

type Review' s a = Review s s a a


-- Construction

unto :: (b -> t) -> Review s t a b
unto f = lphantom . rmap f


-- Elimination

reviews :: Has (Reader e) sig m => Review s t a b -> (e -> b) -> m t
reviews b = asks . runRecall . b . Recall

review :: Has (Reader b) sig m => Review s t a b -> m t
review o = reviews o id

(<~) :: Review s t a b -> (b -> t)
(<~) = review

infixr 8 <~

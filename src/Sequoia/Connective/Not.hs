module Sequoia.Connective.Not
( -- * Not
  Not(..)
, type (¬)
) where

import Data.Profunctor
import Sequoia.Connective.Bottom
import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Not

newtype Not a r = Not { getNot :: a • Bottom r }
  deriving (Functor)
  deriving (Continuation, ContinuationE, ContinuationI, Profunctor) via (•)

instance Pos a => Polarized N (Not a r) where


type (¬) = Not

infixr 9 ¬

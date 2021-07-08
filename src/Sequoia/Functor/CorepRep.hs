-- | 'Representable' functors from 'Corepresentable' 'Profunctor's.
module Sequoia.Functor.CorepRep
( CorepRep(..)
) where

import Data.Profunctor

newtype CorepRep p s a = CorepRep { getCorepRep :: p s a }
  deriving (Choice, Closed, Cochoice, Costrong, Functor, Profunctor, Strong)

{-# LANGUAGE UndecidableInstances #-}
-- | 'Representable' functors from 'Corepresentable' 'Profunctor's.
module Sequoia.Functor.CorepRep
( CorepRep(..)
) where

import Data.Profunctor
import Data.Profunctor.Sieve

newtype CorepRep p s a = CorepRep { getCorepRep :: p s a }
  deriving (Choice, Closed, Cochoice, Costrong, Functor, Profunctor, Strong)

instance Cosieve p r => Cosieve (CorepRep p) r where
  cosieve = cosieve . getCorepRep

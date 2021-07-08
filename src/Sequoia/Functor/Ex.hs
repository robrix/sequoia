{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
-- | 'Representable' functors from 'Corepresentable' 'Profunctor's.
module Sequoia.Functor.Ex
( CorepRep(..)
) where

import Data.Distributive
import Data.Functor.Rep (Representable(..))
import Data.Profunctor
import Data.Profunctor.Rep (Corepresentable(..))
import Data.Profunctor.Sieve

newtype CorepRep p s a = CorepRep { getCorepRep :: p s a }
  deriving (Choice, Closed, Cochoice, Costrong, Functor, Profunctor, Strong)

instance Cosieve p r => Cosieve (CorepRep p) r where
  cosieve = cosieve . getCorepRep

instance Corepresentable p => Corepresentable (CorepRep p) where
  type Corep (CorepRep p) = Corep p
  cotabulate = CorepRep . cotabulate

instance Distributive (p s) => Distributive (CorepRep p s) where
  distribute = CorepRep . distribute . fmap getCorepRep
  collect f = CorepRep . collect (getCorepRep . f)

instance (Distributive (p s), Corepresentable p) => Representable (CorepRep p s) where
  type Rep (CorepRep p s) = Corep p s
  tabulate = cotabulate
  index = cosieve

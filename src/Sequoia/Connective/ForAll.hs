module Sequoia.Connective.ForAll
( -- * Universal quantification
  ForAll(..)
  -- * Construction
, forAll
) where

import Sequoia.Polarity
import Sequoia.Profunctor.Continuation

-- Universal quantification

newtype ForAll r p f = ForAll { runForAll :: forall x . Polarized p x => f x •• r }

instance Polarized N (ForAll r p f)


-- Construction

forAll :: (forall x . Polarized p x => f x) -> ForAll r p f
forAll f = ForAll (dn f)

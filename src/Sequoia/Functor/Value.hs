{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Functor.Value
( -- * Values
  Value
, V(..)
  -- * Construction
, inV0
, inV
, idV
  -- * Coercion
, _V
  -- * Computation
, (>∘∘<)
, (>∘∘∘<)
, (<∘∘>)
  -- * Ambient environment
, Env(..)
, val
) where

import Data.Functor.Rep
import Sequoia.Profunctor.Value (Env(..), V(..), _V, idV, inV0, val, (<∘∘>), (>∘∘<), (>∘∘∘<))

-- Values

class Representable v => Value v


-- Construction

inV :: (e -> a) -> V e a
inV = tabulate

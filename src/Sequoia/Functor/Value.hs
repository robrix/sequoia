{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Functor.Value
( -- * Values
  V(..)
  -- * Construction
, inV0
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

import Sequoia.Profunctor.Value (Env(..), V(..), _V, idV, inV0, val, (<∘∘>), (>∘∘<), (>∘∘∘<))

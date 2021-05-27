{-# LANGUAGE TemplateHaskell #-}
module Focalized.Multiset.Test
( tests
) where

import qualified Focalized.Multiset as S
import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

tests :: IO Bool
tests = checkParallel $$(discover)

prop_semigroup_associativity = property $ do
  (a, b, c) <- (,,) <$> forAll set <*> forAll set <*> forAll set
  a <> (b <> c) === (a <> b) <> c

set = S.fromList <$> Gen.list (Range.linear 0 10) element
element = Gen.choice (map pure ['a'..'z'])

{-# LANGUAGE TemplateHaskell #-}
module Focalized.Multiset.Test
( tests
) where

import           Data.Foldable (for_)
import qualified Focalized.Multiset as S
import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

tests :: IO Bool
tests = checkParallel $$(discover)

prop_semigroup_associativity = property $ do
  (a, b, c) <- (,,) <$> forAll set <*> forAll set <*> forAll set
  a <> (b <> c) === (a <> b) <> c

prop_monoid_left_identity = property $ do
  s <- forAll set
  mappend mempty s === s

prop_monoid_right_identity = property $ do
  s <- forAll set
  mappend s mempty === s

prop_semigroup_commutativity = property $ do
  (a, b) <- (,) <$> forAll set <*> forAll set
  a <> b === b <> a

prop_quotients_length = property $ do
  s <- forAll set
  for_ (S.quotients s) $ \ (_, s') -> length s' === pred (length s)

set = S.fromList <$> Gen.list (Range.linear 0 10) element
element = Gen.choice (map pure ['a'..'z'])

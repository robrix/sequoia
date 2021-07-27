{-# LANGUAGE TemplateHaskell #-}
module Sequoia.Cons.Test
( tests
) where

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Sequoia.Cons as List

tests :: IO Bool
tests = checkParallel $$(discover)

prop_semigroup_associativity = property $ do
  (a, b, c) <- forAll ((,,) <$> genList Gen.alpha <*> genList Gen.alpha <*> genList Gen.alpha)
  ((a <> b) <> c) === (a <> (b <> c))


prop_zip_length_minimum = property $ do
  (as, bs) <- forAll ((,) <$> genList Gen.alpha <*> genList Gen.alpha)
  length (List.zip as bs) === length as `min` length bs


prop_align_length_maximum = property $ do
  (as, bs) <- forAll ((,) <$> genList Gen.alpha <*> genList Gen.alpha)
  length (List.align as bs) === length as `max` length bs


prop_equality = property $ do
  (as, bs) <- forAll ((,) <$> genList Gen.alpha <*> genList Gen.alpha)
  (as == bs) === (toList as == toList bs)


genList :: Gen a -> Gen (List a)
genList = fmap fromList . Gen.list (Range.linear 0 10)

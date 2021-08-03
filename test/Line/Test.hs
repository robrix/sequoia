{-# LANGUAGE TemplateHaskell #-}
module Line.Test
( tests
) where

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import           Sequoia.Line

tests :: IO Bool
tests = checkParallel $$(discover)


prop_line_ending_semigroup_associativity = property $ do
  (a, b, c) <- forAll ((,,) <$> genLineEnding <*> genLineEnding <*> genLineEnding)
  ((a <> b) <> c) === (a <> (b <> c))


genLineEnding :: Gen LineEnding
genLineEnding = Gen.enumBounded

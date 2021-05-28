{-# LANGUAGE TemplateHaskell #-}
module Focalized.Multiset.Test
( tests
) where

import           Data.Foldable (for_)
import           Data.Semigroup (stimes)
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

prop_insert_iteration = property $ do
  i <- forAll (Gen.int (Range.linear 0 10))
  a <- forAll element
  s <- forAll set
  foldl (const . S.insert a) s [0..pred i] === S.insertN a i s

prop_insert_length = property $ do
  a <- forAll element
  s <- forAll set
  length (S.insert a s) === succ (length s)

prop_insert_multiplicity = property $ do
  a <- forAll element
  s <- forAll set
  S.multiplicity a (S.insert a s) === succ (S.multiplicity a s)

prop_insert_inverse = property $ do
  a <- forAll element
  s <- forAll set
  S.delete a (S.insert a s) === s

prop_delete_iteration = property $ do
  i <- forAll (Gen.int (Range.linear 0 10))
  a <- forAll element
  s <- mappend (stimes (succ i) (S.singleton a)) <$> forAll set
  foldl (const . S.delete a) s [0..i] === S.deleteN a (succ i) s

prop_delete_multiplicity = property $ do
  a <- forAll element
  s <- mappend (S.singleton a) <$> forAll set
  S.multiplicity a (S.delete a s) === pred (S.multiplicity a s)

prop_delete_partial_inverse = property $ do
  a <- forAll element
  s <- mappend (S.singleton a) <$> forAll set
  S.insert a (S.delete a s) === s


set = S.fromList <$> Gen.list (Range.linear 0 10) element
element = Gen.choice (map pure ['a'..'z'])

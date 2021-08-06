{-# LANGUAGE TypeFamilies #-}
module Sequoia.Birepresentable
( -- * Birepresentable functors
  Birepresentable(..)
) where

import Sequoia.Bidistributive

class Bidistributive p => Birepresentable p where
  type Birep p
  bitabulate :: (Birep p -> a) -> (Birep p -> b) -> p a b
  biindex :: p a b -> (Birep p -> Either a b)

instance Birepresentable (,) where
  type Birep (,) = Bool
  bitabulate f g = (f False, g True)
  biindex p = \case
    False -> Left  (fst p)
    True  -> Right (snd p)

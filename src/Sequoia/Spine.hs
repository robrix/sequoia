{-# LANGUAGE GADTs #-}
module Sequoia.Spine
( -- * Spines
  Spine(..)
, viewR
, ViewR(..)
) where

import qualified Control.Category as Cat

-- Spines

data Spine arr a b where
  Id :: Spine arr a a
  (:.) :: Spine arr a b -> arr b c -> Spine arr a c

infixl 9 :.

instance Cat.Category (Spine arr) where
  id = Id
  fs . gs = case fs of
    Id    -> gs
    fs:.f -> (gs Cat.>>> fs) :. f


viewR :: Spine arr a b -> ViewR arr a b
viewR = \case
  Id     -> NilR
  i :. l -> i :> l

data ViewR arr a b where
  NilR :: ViewR arr a a
  (:>) :: Spine arr a b -> arr b c -> ViewR arr a c

{-# LANGUAGE GADTs #-}
module Sequoia.Spine
( -- * Spines
  Spine(..)
) where

import qualified Control.Category as Cat

-- Spines

data Spine arr a b where
  Nil :: Spine arr a a
  (:>) :: Spine arr a b -> arr b c -> Spine arr a c

infixl 5 :>

instance Cat.Category (Spine arr) where
  id = Nil
  fs . gs = case fs of
    Nil   -> gs
    fs:>f -> (gs Cat.>>> fs) :> f

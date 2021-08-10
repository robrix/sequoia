{-# LANGUAGE GADTs #-}
module Sequoia.Spine
( -- * Spines
  Spine(..)
) where

data Spine arr a b where
  Nil :: Spine arr a a
  (:>) :: Spine arr a b -> arr b c -> Spine arr a c

infixl 5 :>

module Sequoia.Functor.V
( V(..)
) where

newtype V s a = V { runV :: s -> a }

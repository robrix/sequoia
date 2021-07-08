module Sequoia.Confunctor
( Confunctor(..)
) where

class Confunctor p where
  conmap :: (a -> a') -> (b' -> b) -> ((a `p` b) -> (a' `p` b'))

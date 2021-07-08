module Sequoia.Confunctor
( Confunctor(..)
) where

class Confunctor p where
  conmap :: (a -> a') -> (b' -> b) -> ((a `p` b) -> (a' `p` b'))

  mapl :: (a -> a') -> ((a `p` b) -> (a' `p` b))
  mapr :: (b' -> b) -> ((a `p` b) -> (a `p` b'))

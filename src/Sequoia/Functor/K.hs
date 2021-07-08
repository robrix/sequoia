module Sequoia.Functor.K
( K(..)
) where

newtype K r a = K { runK :: a -> r }

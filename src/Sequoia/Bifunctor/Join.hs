module Sequoia.Bifunctor.Join
( Join(..)
) where

newtype Join p a = Join { runJoin :: p a a }

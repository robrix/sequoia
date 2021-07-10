module Sequoia.Profunctor.D
( KV(..)
) where

newtype KV s r a = KV { runKV :: a -> s -> r }

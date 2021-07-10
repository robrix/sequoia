module Sequoia.Profunctor.D
( _KV
, KV(..)
) where

import Sequoia.Bijection

_KV :: Optic Iso (KV s r a) (KV s' r' a') (a -> s -> r) (a' -> s' -> r')
_KV = runKV <-> KV

newtype KV s r a = KV { runKV :: a -> s -> r }

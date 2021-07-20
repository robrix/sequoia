module Sequoia.Profunctor.Exchange
( -- * Exchange profunctor
  Exchange(..)
  -- * Construction
, idExchange
  -- * Elimination
, withExchange
) where

import Data.Profunctor

-- Exchange profunctor

data Exchange a b s t = Exchange (s -> a) (b -> t)
  deriving (Functor)

instance Profunctor (Exchange a b) where
  dimap f g (Exchange sa bt) = Exchange (sa . f) (g . bt)


-- Construction

idExchange :: Exchange a b a b
idExchange = Exchange id id


-- Elimination

withExchange :: Exchange a b s t -> (((s -> a) -> (b -> t) -> r) -> r)
withExchange (Exchange sa bt) f = f sa bt

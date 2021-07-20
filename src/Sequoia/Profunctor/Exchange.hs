module Sequoia.Profunctor.Exchange
( -- * Exchange profunctor
  Exchange(..)
  -- * Construction
, exchange
, idExchange
  -- * Elimination
, runExchange
) where

import Data.Profunctor

-- Exchange profunctor

newtype Exchange a b s t = Exchange { withExchange :: forall r . ((s -> a) -> (b -> t) -> r) -> r }
  deriving (Functor)

instance Profunctor (Exchange a b) where
  dimap f g e = withExchange e (\ sa bt -> exchange (sa . f) (g . bt))


-- Construction

exchange :: (s -> a) -> (b -> t) -> Exchange a b s t
exchange v r = Exchange (\ f -> f v r)

idExchange :: Exchange a b a b
idExchange = exchange id id


-- Elimination

runExchange :: Exchange a b s t -> ((a -> b) -> (s -> t))
runExchange e = withExchange e (\ sa bt -> (bt .) . (. sa))

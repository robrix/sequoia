module Sequoia.Profunctor.Exchange
( Exchange(..)
) where

data Exchange a b s t = Exchange (s -> a) (b -> t)

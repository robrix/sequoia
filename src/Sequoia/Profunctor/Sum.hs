{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Profunctor.Sum
( (:+:)(..)
) where

import qualified Control.Arrow as A ((+++))
import           Data.Functor.Sum
import           Data.Profunctor
import           Data.Profunctor.Sieve

newtype (p :+: q) a b = Sum { runSum :: Either (p a b) (q a b) }

infixr 5 :+:

instance (Profunctor p, Profunctor q) => Profunctor (p :+: q) where
  dimap f g = Sum . (dimap f g A.+++ dimap f g) . runSum

instance (Strong p, Strong q) => Strong (p :+: q) where
  first'  = Sum . (first'  A.+++ first' ) . runSum
  second' = Sum . (second' A.+++ second') . runSum

instance (Costrong p, Costrong q) => Costrong (p :+: q) where
  unfirst  = Sum . (unfirst  A.+++ unfirst ) . runSum
  unsecond = Sum . (unsecond A.+++ unsecond) . runSum

instance (Choice p, Choice q) => Choice (p :+: q) where
  left'  = Sum . (left'  A.+++ left' ) . runSum
  right' = Sum . (right' A.+++ right') . runSum

instance (Cochoice p, Cochoice q) => Cochoice (p :+: q) where
  unleft  = Sum . (unleft  A.+++ unleft ) . runSum
  unright = Sum . (unright A.+++ unright) . runSum

instance (Closed p, Closed q) => Closed (p :+: q) where
  closed = Sum . (closed A.+++ closed) . runSum

instance (Sieve p f, Sieve q g) => Sieve (p :+: q) (Sum f g) where
  sieve (Sum s) a = either (InL . (`sieve` a)) (InR . (`sieve` a)) s

instance (Cosieve p f, Cosieve q f) => Cosieve (p :+: q) f where
  cosieve (Sum s) a = either (`cosieve` a) (`cosieve` a) s

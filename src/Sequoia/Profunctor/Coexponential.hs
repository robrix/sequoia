{-# LANGUAGE QuantifiedConstraints #-}
module Sequoia.Profunctor.Coexponential
( -- * Coexponential profunctor
  Coexp(..)
  -- * Construction
, idCoexp
  -- * Elimination
, withCoexp
, runCoexp
, unCoexp
, evalCoexp
  -- * Optics
, recall_
, forget_
) where

import Data.Profunctor
import Sequoia.Optic.Lens
import Sequoia.Profunctor.Context
import Sequoia.Profunctor.Continuation
import Sequoia.Profunctor.Value

-- Coexponential profunctor

data Coexp e r a b = Coexp { recall :: e ∘ b, forget :: a • r }
  deriving (Functor)

instance Profunctor (Coexp e r) where
  dimap g h (Coexp r f) = Coexp (fmap h r) (lmap g f)


-- Construction

idCoexp :: Coexp b a a b
idCoexp = Coexp idV idK


-- Elimination

withCoexp :: Coexp e r a b -> (e ∘ b -> a • r -> s) -> s
withCoexp c f = f (recall c) (forget c)

runCoexp :: Coexp e r b a -> ((a -> b) -> (e -> r))
runCoexp c = withCoexp c (\ r f -> ((f •) .) . (. (r ∘)))

unCoexp :: (e ∘ a -> b • r -> s) -> Coexp e r b a -> s
unCoexp = flip withCoexp

evalCoexp :: Coexp e r a a -> e ==> r
evalCoexp = unCoexp (flip (•∘))


-- Optics

recall_ :: Lens (Coexp e r a b) (Coexp e' r a b') (e ∘ b) (e' ∘ b')
recall_ = lens recall (\ s recall -> s{ recall })

forget_ :: Lens (Coexp e r a b) (Coexp e r' a' b) (a • r) (a' • r')
forget_ = lens forget (\ s forget -> s{ forget })

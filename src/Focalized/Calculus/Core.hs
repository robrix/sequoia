{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
module Focalized.Calculus.Core
( -- * Core
  Core(..)
  -- * Structural
, Structural
, Weaken(..)
, wkL'
, wkR'
, Contract(..)
, Exchange(..)
  -- * Contextual
, Contextual(..)
) where

import Control.Monad (join)
import Data.Functor.Contravariant
import Focalized.CPS
import Focalized.Calculus.Context
import Prelude hiding (init)

class Core s where
  {-# MINIMAL ((>>>) | (<<<)), init #-}

  (>>>)
    :: i -|s r|- o > a   ->   a < i -|s r|- o
    -- --------------------------------------
    -> i -|s r|- o
  (>>>) = flip (<<<)

  (<<<)
    :: a < i -|s r|- o   ->   i -|s r|- o > a
    -- --------------------------------------
    -> i -|s r|- o
  (<<<) = flip (>>>)

  infixr 1 >>>, <<<

  init
    -- -------------------
    :: a < i -|s r|- o > a


-- Structural

type Structural s = (Weaken s, Contract s, Exchange s)


class Core s => Weaken s where
  wkL
    ::     i -|s r|- o
    -- ---------------
    -> a < i -|s r|- o
  default wkL
    :: Contextual s
    =>     i -|s r|- o
    -- ---------------
    -> a < i -|s r|- o
  wkL = popL . const

  wkR
    :: i -|s r|- o
    -- ---------------
    -> i -|s r|- o > a
  default wkR
    :: Contextual s
    => i -|s r|- o
    -- ---------------
    -> i -|s r|- o > a
  wkR = popR . const


wkL'
  :: (Weaken s, Exchange s)
  => a     < i -|s r|- o
  -- -------------------
  -> a < b < i -|s r|- o
wkL' = exL . wkL

wkR'
  :: (Weaken s, Exchange s)
  => i -|s r|- o > a
  -- -------------------
  -> i -|s r|- o > b > a
wkR' = exR . wkR


class Core s => Contract s where
  cnL
    :: a < a < i -|s r|- o
    -- -------------------
    ->     a < i -|s r|- o
  default cnL
    :: Contextual s
    => a < a < i -|s r|- o
    -- -------------------
    ->     a < i -|s r|- o
  cnL = popL . join . pushL2

  cnR
    :: i -|s r|- o > a > a
    -- -------------------
    -> i -|s r|- o > a
  default cnR
    :: Contextual s
    => i -|s r|- o > a > a
    -- -------------------
    -> i -|s r|- o > a
  cnR = popR . join . pushR2


class Core s => Exchange s where
  exL
    :: a < b < c -|s r|- o
    -- -------------------
    -> b < a < c -|s r|- o
  default exL
    :: Contextual s
    => a < b < c -|s r|- o
    -- -------------------
    -> b < a < c -|s r|- o
  exL = popL2 . flip . pushL2

  exR
    :: i -|s r|- o > a > b
    -- -------------------
    -> i -|s r|- o > b > a
  default exR
    :: Contextual s
    => i -|s r|- o > a > b
    -- -------------------
    -> i -|s r|- o > b > a
  exR = popR2 . flip . pushR2


class Core s => Contextual s where
  -- | Pop something off the input context which can later be pushed. Used with 'pushL', this provides a generalized context restructuring facility.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  popL :: (a -> s r i o) -> s r (a < i) o

  poppedL :: (s r i o -> s r i' o') -> (s r (a < i) o -> s r (a < i') o')
  poppedL f p = popL (f . pushL p)

  -- | Push something onto the input context which was previously popped off it. Used with 'popL', this provides a generalized context restructuring facility. It i undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  pushL :: s r (a < i) o -> (a -> s r i o)

  popL2 :: (a -> b -> s r i o) -> s r (a < b < i) o
  popL2 f = popL (popL . f)

  pushL2 :: s r (a < b < i) o -> a -> b -> s r i o
  pushL2 p = pushL . pushL p

  mapL :: (a' -> a) -> s r (a < i) o -> s r (a' < i) o
  mapL f p = popL (pushL p . f)

  -- FIXME: this is clearly possible, tho it’s less clear that it’s a good idea.
  -- mapL2 :: (c -> (b, a)) -> s r (a < i) o -> s r (b < i) o -> s r (c < i) o
  -- mapL2 f a b = popL (pushL b . exl . f) <> popL (pushL a . exr . f)

  liftL :: r •a -> s r (a < i) o
  liftL = pushR init

  lowerL :: (r •a -> s r i o) -> (s r (a < i) o -> s r i o)
  lowerL k p = popR k >>> p


  -- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  popR :: (r •a -> s r i o) -> s r i (o > a)

  poppedR :: (s r i o -> s r i' o') -> (s r i (o > a) -> s r i' (o' > a))
  poppedR f p = popR (f . pushR p)

  -- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It i undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  pushR :: s r i (o > a) -> (r •a -> s r i o)

  popR2 :: (r •a -> r •b -> s r i o) -> s r i (o > b > a)
  popR2 f = popR (popR . f)

  pushR2 :: s r i (o > b > a) -> r •a -> r •b -> s r i o
  pushR2 p = pushR . pushR p

  mapR :: (a -> a') -> s r i (o > a) -> s r i (o > a')
  mapR f p = popR (pushR p . contramap f)

  mapR2 :: (a -> b -> c) -> s r i (o > a) -> s r i (o > b) -> s r i (o > c)
  default mapR2 :: (Weaken s, Exchange s) => (a -> b -> c) -> s r i (o > a) -> s r i (o > b) -> s r i (o > c)
  mapR2 f a b = popR (pushR (wkR' a) . contramap f) >>> popL (\ f -> popR (pushR b . contramap f))

  liftR :: a -> s r i (o > a)
  liftR = pushL init

  lowerR :: (a -> s r i o) -> (s r i (o > a) -> s r i o)
  lowerR k p = p >>> popL k

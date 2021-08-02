module Sequoia.Syntax
( Expr(..)
) where

import Sequoia.Polarity

class Expr r where
  intop :: r N
  inwith :: r N -> r N -> r N
  exwithL :: r N -> r N
  exwithR :: r N -> r N
  inpar :: r N -> r N -> r N
  expar :: (r N -> r o) -> (r N -> r o) -> (r N -> r o)
  innot :: r P -> r N

  inone :: r P
  insumL :: r P -> r P
  insumR :: r P -> r P
  exsum :: (r P -> r o) -> (r P -> r o) -> (r P -> r o)
  intensor :: r P -> r P -> r P
  extensor :: (r P -> r P -> r o) -> (r P -> r o)
  innegate :: r N -> r P

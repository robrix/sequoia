module Sequoia.Syntax
( Expr(..)
) where

import Sequoia.Polarity

class Expr r where
  top :: r N
  with :: r N -> r N -> r N
  par :: r N -> r N -> r N
  not :: r P -> r N

  one :: r P
  sumL :: r P -> r P
  sumR :: r P -> r P
  tensor :: r P -> r P -> r P
  negate :: r N -> r P

module Sequoia.Syntax
( Expr(..)
) where

import Sequoia.Connective.Negate
import Sequoia.Connective.Not
import Sequoia.Connective.One
import Sequoia.Connective.Par
import Sequoia.Connective.Sum
import Sequoia.Connective.Tensor
import Sequoia.Connective.Top
import Sequoia.Connective.With

class Expr rep where
  intop :: rep Top
  inwith :: rep a -> rep b -> rep (a & b)
  exwithL :: rep (a & b) -> rep a
  exwithR :: rep (a & b) -> rep b
  inpar :: rep a -> rep b -> rep (a ⅋ b)
  expar :: (rep a -> rep o) -> (rep b -> rep o) -> (rep (a ⅋ b) -> rep o)
  innot :: rep a -> rep (Not r a)

  inone :: rep (One e)
  insumL :: rep a -> rep (a ⊕ b)
  insumR :: rep b -> rep (a ⊕ b)
  exsum :: (rep a -> rep o) -> (rep b -> rep o) -> (rep (a ⊕ b) -> rep o)
  intensor :: rep a -> rep b -> rep (a ⊗ b)
  extensor :: (rep a -> rep b -> rep o) -> (rep (a ⊗ b) -> rep o)
  innegate :: rep a -> rep (Negate e r a)

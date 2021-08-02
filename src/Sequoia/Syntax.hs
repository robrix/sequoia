{-# LANGUAGE FunctionalDependencies #-}
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

class Expr e r rep | rep -> e r where
  top :: rep Top
  (&) :: rep a -> rep b -> rep (a & b)
  exlN :: rep (a & b) -> rep a
  exrN :: rep (a & b) -> rep b
  par :: (forall x . (rep a -> rep x) -> (rep b -> rep x) -> rep x) -> rep (a ⅋ b)
  exlrN :: rep (a ⅋ b) -> (rep a -> rep o) -> (rep b -> rep o) -> rep o
  not :: rep a -> rep (Not r a)

  one :: rep (One e)
  inlP :: rep a -> rep (a ⊕ b)
  inrP :: rep b -> rep (a ⊕ b)
  exlrP :: rep (a ⊕ b) -> (rep a -> rep o) -> (rep b -> rep o) -> rep o
  (⊗) :: rep a -> rep b -> rep (a ⊗ b)
  extensor :: rep (a ⊗ b) -> (rep a -> rep b -> rep o) -> rep o
  negate :: rep a -> rep (Negate e r a)

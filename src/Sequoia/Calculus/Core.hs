module Sequoia.Calculus.Core
( -- * Core
  Core(..)
) where

import Sequoia.Calculus.Context

-- Core

class Core s where
  {-# MINIMAL ((>>>) | (<<<)), init #-}

  (>>>)
    :: _Γ ⊣s e r⊢ _Δ > a   ->   a < _Γ ⊣s e r⊢ _Δ
    -- ----------------------------------------------
    ->             _Γ ⊣s e r⊢ _Δ
  (>>>) = flip (<<<)

  (<<<)
    :: a < _Γ ⊣s e r⊢ _Δ   ->   _Γ ⊣s e r⊢ _Δ > a
    -- ----------------------------------------------
    ->             _Γ ⊣s e r⊢ _Δ
  (<<<) = flip (>>>)

  infixr 1 >>>, <<<

  init
    -- -----------------------
    :: a < _Γ ⊣s e r⊢ _Δ > a

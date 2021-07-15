module Sequoia.Calculus.Function
( -- * Function
  FunctionIntro(..)
, funL2
, ($$)
, funR'
, funLPar
, funRPar
  -- * Connectives
, module Sequoia.Connective.Function
) where

import Prelude hiding (init)
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Not
import Sequoia.Calculus.Par
import Sequoia.Connective.Function
import Sequoia.Polarity

-- Function

class Core e r s => FunctionIntro e r s where
  funL, (->⊢)
    :: (Pos a, Neg b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->     a ~~Fun e r~> b < _Γ -|s|- _Δ
  (->⊢) = funL

  infixr 5 ->⊢

  funR
    :: (Pos a, Neg b)
    => a < _Γ -|s|- _Δ > b
    -- ---------------------------------
    ->     _Γ -|s|- _Δ > a ~~Fun e r~> b


funL2
  :: (FunctionIntro e r s, Pos a, Neg b)
  -- -------------------------------------
  => a ~~Fun e r~> b < a < _Γ -|s|- _Δ > b
funL2 = init ->⊢ init

($$)
  :: (Weaken e r s, Exchange e r s, FunctionIntro e r s, Pos a, Neg b)
  => _Γ -|s|- _Δ > a ~~Fun e r~> b   ->   _Γ -|s|- _Δ > a
  -- ----------------------------------------------------
  ->                  _Γ -|s|- _Δ > b
f $$ a = wkR' f >>> wkR' a ->⊢ init

funR'
  :: (Weaken e r s, Exchange e r s, FunctionIntro e r s, Pos a, Neg b)
  =>     _Γ -|s|- _Δ > a ~~Fun e r~> b
  ------------------------------------
  -> a < _Γ -|s|- _Δ > b
funR' p = wkL (wkR' p) >>> funL2

funLPar
  :: (Weaken e r s, Exchange e r s, FunctionIntro e r s, ParIntro e r s, NotIntro e r s, Pos a, Neg b)
  =>        r ¬a ⅋ b < _Γ -|s|- _Δ
  -- -----------------------------
  -> a ~~Fun e r~> b < _Γ -|s|- _Δ
funLPar s = parR (exR (notR (exL (init ->⊢ init)))) >>> wkL' s

funRPar
  :: (Weaken e r s, Exchange e r s, FunctionIntro e r s, ParIntro e r s, NotIntro e r s, Pos a, Neg b)
  => _Γ -|s|- _Δ > r ¬a ⅋ b
  -- -----------------------------
  -> _Γ -|s|- _Δ > a ~~Fun e r~> b
funRPar s = wkR' s >>> funR (exL (notL init ⅋⊢ init))

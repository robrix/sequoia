module Focalized.Calculus.Function
( -- * Function
  FunctionIntro(..)
, funL2
, ($$)
, funR'
, funRPar
  -- * Connectives
, module Focalized.Connective.Function
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Not
import Focalized.Calculus.Par
import Focalized.Connective.Function
import Focalized.Polarity
import Prelude hiding (init)

-- Function

class FunctionIntro s where
  funL, (->⊢)
    :: (Pos a, Neg b)
    => _Γ -|s r|- _Δ > a   ->   b < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->        a ~~r~> b < _Γ -|s r|- _Δ
  (->⊢) = funL

  infixr 5 ->⊢

  funR
    :: (Pos a, Neg b)
    => a < _Γ -|s r|- _Δ > b
    -- -----------------------------
    ->     _Γ -|s r|- _Δ > a ~~r~> b


funL2
  :: (Core s, FunctionIntro s, Pos a, Neg b)
  -- ---------------------------------
  => a ~~r~> b < a < _Γ -|s r|- _Δ > b
funL2 = funL init init

($$)
  :: (Weaken s, Exchange s, FunctionIntro s, Pos a, Neg b)
  => _Γ -|s r|- _Δ > a ~~r~> b   ->   _Γ -|s r|- _Δ > a
  -- --------------------------------------------------
  ->                _Γ -|s r|- _Δ > b
f $$ a = wkR' f >>> wkR' a `funL` init

funR'
  :: (Weaken s, Exchange s, FunctionIntro s, Pos a, Neg b)
  =>     _Γ -|s r|- _Δ > a ~~r~> b
  -- -----------------------------
  -> a < _Γ -|s r|- _Δ > b
funR' p = wkL (wkR' p) >>> funL2

funRPar
  :: (Weaken s, Exchange s, FunctionIntro s, ParIntro s, NotIntro s, Pos a, Neg b)
  => _Γ -|s r|- _Δ > r ¬a ⅋ b
  -- -------------------------
  -> _Γ -|s r|- _Δ > a ~~r~> b
funRPar s = wkR' s >>> funR (exL (notL init ⅋⊢ init))

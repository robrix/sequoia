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

class Core r e s => FunctionIntro r e s where
  funL, (->⊢)
    :: (Pos a, Neg b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->     a ~~Fun r e~> b < _Γ -|s|- _Δ
  (->⊢) = funL

  infixr 5 ->⊢

  funR
    :: (Pos a, Neg b)
    => a < _Γ -|s|- _Δ > b
    -- ---------------------------------
    ->     _Γ -|s|- _Δ > a ~~Fun r e~> b


funL2
  :: (FunctionIntro r e s, Pos a, Neg b)
  -- -------------------------------------
  => a ~~Fun r e~> b < a < _Γ -|s|- _Δ > b
funL2 = init ->⊢ init

($$)
  :: (Weaken r e s, Exchange r e s, FunctionIntro r e s, Pos a, Neg b)
  => _Γ -|s|- _Δ > a ~~Fun r e~> b   ->   _Γ -|s|- _Δ > a
  -- ----------------------------------------------------
  ->                  _Γ -|s|- _Δ > b
f $$ a = wkR' f >>> wkR' a ->⊢ init

funR'
  :: (Weaken r e s, Exchange r e s, FunctionIntro r e s, Pos a, Neg b)
  =>     _Γ -|s|- _Δ > a ~~Fun r e~> b
  ------------------------------------
  -> a < _Γ -|s|- _Δ > b
funR' p = wkL (wkR' p) >>> funL2

funLPar
  :: (Weaken r e s, Exchange r e s, FunctionIntro r e s, ParIntro r e s, NotIntro r e s, Pos a, Neg b)
  =>        r ¬a ⅋ b < _Γ -|s|- _Δ
  -- -----------------------------
  -> a ~~Fun r e~> b < _Γ -|s|- _Δ
funLPar s = parR (exR (notR (exL (init ->⊢ init)))) >>> wkL' s

funRPar
  :: (Weaken r e s, Exchange r e s, FunctionIntro r e s, ParIntro r e s, NotIntro r e s, Pos a, Neg b)
  => _Γ -|s|- _Δ > r ¬a ⅋ b
  -- -----------------------------
  -> _Γ -|s|- _Δ > a ~~Fun r e~> b
funRPar s = wkR' s >>> funR (exL (notL init ⅋⊢ init))

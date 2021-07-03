module Focalized.Calculus.Function
( -- * Function
  FunctionIntro(..)
, funL2
, ($$)
, funR'
, funLPar
, funRPar
  -- * Connectives
, module Focalized.Connective.Function
) where

import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Not
import Focalized.Calculus.Par
import Focalized.Connective.Function
import Focalized.Continuation
import Focalized.Polarity
import Prelude hiding (init)

-- Function

class Core s => FunctionIntro s where
  funL, (->⊢)
    :: (Pos a, Neg b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->      a ~~R (K s)~> b < _Γ -|s|- _Δ
  (->⊢) = funL

  infixr 5 ->⊢

  funR
    :: (Pos a, Neg b)
    => a < _Γ -|s|- _Δ > b
    -- ---------------------------------
    ->     _Γ -|s|- _Δ > a ~~R (K s)~> b


funL2
  :: (FunctionIntro s, Pos a, Neg b)
  -- -------------------------------------
  => a ~~R (K s)~> b < a < _Γ -|s|- _Δ > b
funL2 = init ->⊢ init

($$)
  :: (Weaken s, Exchange s, FunctionIntro s, Pos a, Neg b)
  => _Γ -|s|- _Δ > a ~~R (K s)~> b   ->   _Γ -|s|- _Δ > a
  -- ----------------------------------------------------
  ->                  _Γ -|s|- _Δ > b
f $$ a = wkR' f >>> wkR' a ->⊢ init

funR'
  :: (Weaken s, Exchange s, FunctionIntro s, Pos a, Neg b)
  =>     _Γ -|s|- _Δ > a ~~R (K s)~> b
  ------------------------------------
  -> a < _Γ -|s|- _Δ > b
funR' p = wkL (wkR' p) >>> funL2

funLPar
  :: (Weaken s, Exchange s, FunctionIntro s, ParIntro s, NotIntro s, Pos a, Neg b)
  =>  R (K s) ¬a ⅋ b < _Γ -|s|- _Δ
  -- -----------------------------
  -> a ~~R (K s)~> b < _Γ -|s|- _Δ
funLPar s = exR (parR (exR (notR (exR init)))) ->⊢ parR init >>> wkL' s

funRPar
  :: (Weaken s, Exchange s, FunctionIntro s, ParIntro s, NotIntro s, Pos a, Neg b)
  => _Γ -|s|- _Δ >  R (K s) ¬a ⅋ b
  -- -----------------------------
  -> _Γ -|s|- _Δ > a ~~R (K s)~> b
funRPar s = wkR' s >>> funR (exL (notL init ⅋⊢ init))

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

class Core k s => FunctionIntro k s where
  funL, (->⊢)
    :: (Pos a, Neg b)
    => _Γ -|s|- _Δ > a   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->        a ~~k~> b < _Γ -|s|- _Δ
  (->⊢) = funL

  infixr 5 ->⊢

  funR
    :: (Pos a, Neg b)
    => a < _Γ -|s|- _Δ > b
    -- -----------------------------
    ->     _Γ -|s|- _Δ > a ~~k~> b


funL2
  :: (FunctionIntro k s, Pos a, Neg b)
  -- ---------------------------------
  => a ~~k~> b < a < _Γ -|s|- _Δ > b
funL2 = init ->⊢ init

($$)
  :: (Weaken k s, Exchange k s, FunctionIntro k s, Pos a, Neg b)
  => _Γ -|s|- _Δ > a ~~k~> b   ->   _Γ -|s|- _Δ > a
  -- ------------------------------------------------
  ->                  _Γ -|s|- _Δ > b
f $$ a = wkR' f >>> wkR' a ->⊢ init

funR'
  :: (Weaken k s, Exchange k s, FunctionIntro k s, Pos a, Neg b)
  =>     _Γ -|s|- _Δ > a ~~k~> b
  --------------------------------
  -> a < _Γ -|s|- _Δ > b
funR' p = wkL (wkR' p) >>> funL2

funLPar
  :: (Weaken k s, Exchange k s, FunctionIntro k s, ParIntro k s, NotIntro k s, Pos a, Neg b)
  =>  k ¬a ⅋ b < _Γ -|s|- _Δ
  -- -------------------------
  -> a ~~k~> b < _Γ -|s|- _Δ
funLPar s = parR (exR (notR (exL (init ->⊢ init)))) >>> wkL' s

funRPar
  :: (Weaken k s, Exchange k s, FunctionIntro k s, ParIntro k s, NotIntro k s, Pos a, Neg b)
  => _Γ -|s|- _Δ > k ¬a ⅋ b
  -- -------------------------
  -> _Γ -|s|- _Δ > a ~~k~> b
funRPar s = wkR' s >>> funR (exL (notL init ⅋⊢ init))

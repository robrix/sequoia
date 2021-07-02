module Focalized.Calculus.Par
( -- * Par
  ParIntro(..)
, parR'
, parIdentityL
, parIdentityR
, parAssociativity
, parCommutativity
  -- * Connectives
, module Focalized.Par
) where

import Focalized.Calculus.Bottom
import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Par
import Focalized.Polarity
import Prelude hiding (init)

-- Par

class ParIntro s where
  parL
    :: (Neg a, Neg b)
    => a < _Γ -|s r|- _Δ   ->   b < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->          a ⅋ b < _Γ -|s r|- _Δ

  parR
    :: (Neg a, Neg b)
    => _Γ -|s r|- _Δ > a > b
    -- ---------------------
    -> _Γ -|s r|- _Δ > a ⅋ b


parR'
  :: (Weaken s, Contextual s, ParIntro s, Neg a, Neg b)
  => _Γ -|s r|- _Δ > a ⅋ b
  -- ---------------------
  -> _Γ -|s r|- _Δ > a > b
parR' p = poppedR (wkR . wkR) p >>> parL (wkR init) init


parIdentityL
  :: (Core s, ParIntro s, BottomIntro s, Neg a)
  -- ---------------------------
  => Bot ⅋ a < _Γ -|s r|- _Δ > a
parIdentityL = parL botL init

parIdentityR
  :: (Core s, ParIntro s, BottomIntro s, Neg a)
  -- ---------------------------
  => a < _Γ -|s r|- _Δ > a ⅋ Bot
parIdentityR = parR (botR init)

parAssociativity
  :: (Weaken s, Exchange s, ParIntro s, Neg a, Neg b, Neg c)
  -- -----------------------------------------
  => a ⅋ (b ⅋ c) < _Γ -|s r|- _Δ > (a ⅋ b) ⅋ c
parAssociativity = parR (exR (parR (parL (exR init) (parL init (wkR (exR init))))))

parCommutativity
  :: (Exchange s, ParIntro s, Neg a, Neg b)
  -- -----------------------------
  => a ⅋ b < _Γ -|s r|- _Δ > b ⅋ a
parCommutativity = parR (parL init (exR init))

module Focalized.Calculus.Par
( -- * Par
  ParIntro(..)
, parR'
, parIdentityL
, parIdentityR
, parAssociativity
, parCommutativity
, parDistributivityL
, parDistributivityR
, parAnnihilationL
, parAnnihilationR
  -- * Connectives
, module Focalized.Par
) where

import Focalized.Calculus.Bottom
import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Top
import Focalized.Calculus.With
import Focalized.Par
import Focalized.Polarity
import Prelude hiding (init)

-- Par

class ParIntro s where
  parL, (⅋⊢)
    :: (Neg a, Neg b)
    => a < _Γ -|s r|- _Δ   ->   b < _Γ -|s r|- _Δ
    -- ------------------------------------------
    ->          a ⅋ b < _Γ -|s r|- _Δ
  (⅋⊢) = parL

  infixr 7 ⅋⊢

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
  -- ------------------------------
  => Bottom ⅋ a < _Γ -|s r|- _Δ > a
parIdentityL = parL botL init

parIdentityR
  :: (Core s, ParIntro s, BottomIntro s, Neg a)
  -- ------------------------------
  => a < _Γ -|s r|- _Δ > a ⅋ Bottom
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

parDistributivityL
  :: (Exchange s, ParIntro s, WithIntro s, Neg a, Neg b, Neg c)
  -- -------------------------------------------
  => a ⅋ c & b ⅋ c < _Γ -|s r|- _Δ > (a & b) ⅋ c
parDistributivityL = parR (exR (withR (withL1 (parL init (exR init))) (withL2 (parL init (exR init)))))

parDistributivityR
  :: (Exchange s, ParIntro s, WithIntro s, Neg a, Neg b, Neg c)
  -- -------------------------------------------
  => a ⅋ (b & c) < _Γ -|s r|- _Δ > a ⅋ b & a ⅋ c
parDistributivityR = withR (parR (parL (exR init) (withL1 init))) (parR (parL (exR init) (withL2 init)))

parAnnihilationL
  :: TopIntro s
  -- -----------------------------
  => Top ⅋ a < _Γ -|s r|- _Δ > Top
parAnnihilationL = topR

parAnnihilationR
  :: (ParIntro s, TopIntro s, Neg a)
  -- -----------------------------
  => Top < _Γ -|s r|- _Δ > a ⅋ Top
parAnnihilationR = parR topR

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
, module Focalized.Connective.Par
) where

import Focalized.Calculus.Bottom
import Focalized.Calculus.Context
import Focalized.Calculus.Core
import Focalized.Calculus.Top
import Focalized.Calculus.With
import Focalized.Connective.Par
import Focalized.Polarity
import Prelude hiding (init)

-- Par

class Core k s => ParIntro k s where
  parL, (⅋⊢)
    :: (Neg a, Neg b)
    => a < _Γ -|s|- _Δ   ->   b < _Γ -|s|- _Δ
    -- --------------------------------------
    ->          a ⅋ b < _Γ -|s|- _Δ
  (⅋⊢) = parL

  infixr 7 ⅋⊢

  parR
    :: (Neg a, Neg b)
    => _Γ -|s|- _Δ > a > b
    -- -------------------
    -> _Γ -|s|- _Δ > a ⅋ b


parR'
  :: (Weaken k s, Contextual k s, ParIntro k s, Neg a, Neg b)
  => _Γ -|s|- _Δ > a ⅋ b
  -- -------------------
  -> _Γ -|s|- _Δ > a > b
parR' p = poppedR (wkR . wkR) p >>> wkR init ⅋⊢ init


parIdentityL
  :: (ParIntro k s, BottomIntro k s, Neg a)
  -- ----------------------------
  => Bottom ⅋ a < _Γ -|s|- _Δ > a
parIdentityL = botL ⅋⊢ init

parIdentityR
  :: (ParIntro k s, BottomIntro k s, Neg a)
  -- ----------------------------
  => a < _Γ -|s|- _Δ > a ⅋ Bottom
parIdentityR = parR (botR init)

parAssociativity
  :: (Weaken k s, Exchange k s, ParIntro k s, Neg a, Neg b, Neg c)
  -- ---------------------------------------
  => a ⅋ (b ⅋ c) < _Γ -|s|- _Δ > (a ⅋ b) ⅋ c
parAssociativity = parR (exR (parR (exR init ⅋⊢ init ⅋⊢ wkR (exR init))))

parCommutativity
  :: (Exchange k s, ParIntro k s, Neg a, Neg b)
  -- ---------------------------
  => a ⅋ b < _Γ -|s|- _Δ > b ⅋ a
parCommutativity = parR (init ⅋⊢ exR init)

parDistributivityL
  :: (Exchange k s, ParIntro k s, WithIntro k s, Neg a, Neg b, Neg c)
  -- -----------------------------------------
  => a ⅋ c & b ⅋ c < _Γ -|s|- _Δ > (a & b) ⅋ c
parDistributivityL = parR (exR (withL1 (init ⅋⊢ exR init) ⊢& withL2 (init ⅋⊢ exR init)))

parDistributivityR
  :: (Exchange k s, ParIntro k s, WithIntro k s, Neg a, Neg b, Neg c)
  -- -----------------------------------------
  => a ⅋ (b & c) < _Γ -|s|- _Δ > a ⅋ b & a ⅋ c
parDistributivityR = parR (exR init ⅋⊢ withL1 init) ⊢& parR (exR init ⅋⊢ withL2 init)

parAnnihilationL
  :: TopIntro k s
  -- ---------------------------
  => Top ⅋ a < _Γ -|s|- _Δ > Top
parAnnihilationL = topR

parAnnihilationR
  :: (ParIntro k s, TopIntro k s, Neg a)
  -- ---------------------------
  => Top < _Γ -|s|- _Δ > a ⅋ Top
parAnnihilationR = parR topR

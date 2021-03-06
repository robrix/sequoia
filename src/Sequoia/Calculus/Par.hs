module Sequoia.Calculus.Par
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
, module Sequoia.Connective.Par
) where

import Prelude hiding (init)
import Sequoia.Calculus.Bottom
import Sequoia.Calculus.Context
import Sequoia.Calculus.Core
import Sequoia.Calculus.Structural
import Sequoia.Calculus.Top
import Sequoia.Calculus.With
import Sequoia.Connective.Par
import Sequoia.Contextual
import Sequoia.Polarity

-- Par

class Core s => ParIntro s where
  parL, (⅋⊢)
    :: (Neg a, Neg b)
    => a < _Γ ⊣s e r⊢ _Δ   ->   b < _Γ ⊣s e r⊢ _Δ
    -- ----------------------------------------------
    ->             a ⅋ b < _Γ ⊣s e r⊢ _Δ
  (⅋⊢) = parL

  infixr 7 ⅋⊢

  parR
    :: (Neg a, Neg b)
    => _Γ ⊣s e r⊢ _Δ > a > b
    -- -----------------------
    -> _Γ ⊣s e r⊢ _Δ > a ⅋ b


parR'
  :: (Weaken s, Contextual s, ParIntro s, Neg a, Neg b)
  => _Γ ⊣s e r⊢ _Δ > a ⅋ b
  -- -----------------------
  -> _Γ ⊣s e r⊢ _Δ > a > b
parR' p = poppedR (wkR . wkR) p >>> wkR init ⅋⊢ init


parIdentityL
  :: (ParIntro s, BottomIntro s, Neg a)
  -- ----------------------------------
  => Bottom r ⅋ a < _Γ ⊣s e r⊢ _Δ > a
parIdentityL = botL ⅋⊢ init

parIdentityR
  :: (ParIntro s, BottomIntro s, Neg a)
  -- ----------------------------------
  => a < _Γ ⊣s e r⊢ _Δ > a ⅋ Bottom r
parIdentityR = parR (botR init)

parAssociativity
  :: (Weaken s, Exchange s, ParIntro s, Neg a, Neg b, Neg c)
  -- -------------------------------------------
  => a ⅋ (b ⅋ c) < _Γ ⊣s e r⊢ _Δ > (a ⅋ b) ⅋ c
parAssociativity = parR (exR (parR (exR init ⅋⊢ init ⅋⊢ wkR (exR init))))

parCommutativity
  :: (Exchange s, ParIntro s, Neg a, Neg b)
  -- -------------------------------
  => a ⅋ b < _Γ ⊣s e r⊢ _Δ > b ⅋ a
parCommutativity = parR (init ⅋⊢ exR init)

parDistributivityL
  :: (Exchange s, ParIntro s, WithIntro s, Neg a, Neg b, Neg c)
  -- ---------------------------------------------
  => a ⅋ c & b ⅋ c < _Γ ⊣s e r⊢ _Δ > (a & b) ⅋ c
parDistributivityL = parR (exR (withL1 (init ⅋⊢ exR init) ⊢& withL2 (init ⅋⊢ exR init)))

parDistributivityR
  :: (Exchange s, ParIntro s, WithIntro s, Neg a, Neg b, Neg c)
  -- ---------------------------------------------
  => a ⅋ (b & c) < _Γ ⊣s e r⊢ _Δ > a ⅋ b & a ⅋ c
parDistributivityR = parR (exR init ⅋⊢ withL1 init) ⊢& parR (exR init ⅋⊢ withL2 init)

parAnnihilationL
  :: TopIntro s
  -- -------------------------------
  => Top ⅋ a < _Γ ⊣s e r⊢ _Δ > Top
parAnnihilationL = topR

parAnnihilationR
  :: (ParIntro s, TopIntro s, Neg a)
  -- -------------------------------
  => Top < _Γ ⊣s e r⊢ _Δ > a ⅋ Top
parAnnihilationR = parR topR

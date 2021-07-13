{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Sequoia.Sequent
( -- * Sequents
  evalSeq
, Seq(..)
, liftLR
, lowerLR
  -- * Effectful sequents
, runSeqT
, SeqT(..)
) where

import qualified Control.Category as Cat
import           Control.Monad.Trans.Class
import           Data.Profunctor
import           Prelude hiding (init)
import           Sequoia.Bijection
import           Sequoia.CPS
import           Sequoia.Calculus.Additive
import           Sequoia.Calculus.Context
import           Sequoia.Calculus.Control
import           Sequoia.Calculus.Core
import           Sequoia.Calculus.Iff
import           Sequoia.Calculus.Implicative
import           Sequoia.Calculus.Mu
import           Sequoia.Calculus.Multiplicative
import           Sequoia.Calculus.Negation
import           Sequoia.Calculus.Nu
import           Sequoia.Calculus.Quantification
import           Sequoia.Calculus.Shift
import           Sequoia.Calculus.XOr
import           Sequoia.Conjunction
import           Sequoia.Continuation
import           Sequoia.Disjunction
import           Sequoia.Functor.K

-- Sequents

evalSeq :: Continuation r k => _Δ ~ KRep k => _Γ -|Seq k|- _Δ -> k _Γ
evalSeq = evalC

newtype Seq k _Γ _Δ = Seq { runSeq :: k _Δ -> k _Γ }
  deriving (Cat.Category, Profunctor) via C k
  deriving (Applicative, Functor, Monad) via C k _Γ

instance Representable k => ContPassing k (Seq k) where
  inC = Seq
  exC = runSeq


liftLR :: ContPassing k c => c a b -> Seq k (a < _Γ) (_Δ > b)
liftLR = dimap exl inr . Seq . exC


lowerLR :: ContPassing k c => (c a b -> _Γ -|Seq k|- _Δ) -> a < _Γ -|Seq k|- _Δ > b -> _Γ -|Seq k|- _Δ
lowerLR f p = inC1' (\ _Δ _Γ -> _Δ ↓ f (inC1' (\ b a -> _Δ ↓ b ↓> p <↑ a • _Γ)) • _Γ)


-- Effectful sequents

runSeqT :: SeqT r _Γ m _Δ -> ((_Δ -> m r) -> (_Γ -> m r))
runSeqT = dimap K runK . runSeq . getSeqT

newtype SeqT r _Γ m _Δ = SeqT { getSeqT :: Seq (K (m r)) _Γ _Δ }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r _Γ) where
  lift m = SeqT (inC1 (const . (m >>=)))


-- Core rules

instance Continuation r k => Core k (Seq k) where
  f >>> g = f >>= pure <--> pushL g

  init = popL liftR


-- Structural rules

deriving via Contextually (Seq k) instance Continuation r k => Weaken   k (Seq k)
deriving via Contextually (Seq k) instance Continuation r k => Contract k (Seq k)
deriving via Contextually (Seq k) instance Continuation r k => Exchange k (Seq k)


-- Contextual rules

instance Continuation r k => Contextual k (Seq k) where
  swapΓΔ f _Δ' _Γ' = inC1' (\ _Δ _Γ -> _Δ' ↓ f _Δ _Γ • _Γ')


-- Control

instance Control Seq where
  reset s = inC (•<< (evalSeq s •))
  shift s = inC1' (\ _Δ -> (inlK _Δ ↓ idK ↓> s <↑ inrK _Δ •))


-- Negation

instance Continuation r k => NotIntro k (Seq k) where
  notL = notLK . kL
  notR = notRK . kR

instance Continuation r k => NegateIntro k (Seq k) where
  negateL = negateLK . kL
  negateR = negateRK . kR


-- Additive

instance Continuation r k => TopIntro k (Seq k) where
  topR = pure (inr Top)

instance Continuation r k => ZeroIntro k (Seq k) where
  zeroL = liftL (inK absurdP)

instance Continuation r k => WithIntro k (Seq k) where
  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = mapR2 inlr

instance Continuation r k => SumIntro k (Seq k) where
  sumL a b = popL (pushL a <--> pushL b)
  sumR1 = mapR inl
  sumR2 = mapR inr


-- Multiplicative

instance Continuation r k => BottomIntro k (Seq k) where
  botL = liftL (inK absurdN)
  botR = wkR

instance Continuation r k => OneIntro k (Seq k) where
  oneL = wkL
  oneR = liftR One

instance Continuation r k => ParIntro k (Seq k) where
  parL a b = popL (pushL a <--> pushL b)
  parR = fmap ((>>= inr . inl) <--> inr . inr)

instance Continuation r k => TensorIntro k (Seq k) where
  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = mapR2 inlr


-- Logical biconditional/exclusive disjunction

instance Continuation r k => IffIntro k (Seq k) where
  iffL1 s1 s2 = mapL getIff (withL1 (downR s1 ->⊢ s2))

  iffL2 s1 s2 = mapL getIff (withL2 (downR s1 ->⊢ s2))

  iffR s1 s2 = mapR Iff (funR (downL s1) ⊢& funR (downL s2))

instance Continuation r k => XOrIntro k (Seq k) where
  xorL s1 s2 = mapL getXOr (subL (upR s1) ⊕⊢ subL (upR s2))

  xorR1 s1 s2 = mapR XOr (sumR1 (s1 ⊢-< upL s2))

  xorR2 s1 s2 = mapR XOr (sumR2 (s1 ⊢-< upL s2))


-- Implication

instance Continuation r k => FunctionIntro k (Seq k) where
  funL a b = popL (\ f -> a >>> liftLR f >>> wkL' b)
  funR = lowerLR liftR . wkR'

instance Continuation r k => SubtractionIntro k (Seq k) where
  subL f = mapL (sub <~) (tensorL (wkL' f >>> poppedL2 negateL init))
  subR a b = mapR (~> sub) (a ⊢⊗ negateR b)


-- Quantification

instance Continuation r k => UniversalIntro k (Seq k) where
  forAllL p = mapL (notNegate . runForAll) p
  forAllR p = inC1' (\ _Δ _Γ -> inrK _Δ • ForAll (inK (\ k -> inlK _Δ ↓ k ↓> p • _Γ)))

instance Continuation r k => ExistentialIntro k (Seq k) where
  existsL p = popL (dnE . runExists (pushL p))
  existsR p = mapR (Exists . liftDN) p


-- Recursion

instance Continuation r k => NuIntro k (Seq k) where
  nuL = mapL runNu
  nuR s = wkR' s >>> existsL (mapL nu init)

instance Continuation r k => MuIntro k (Seq k) where
  muL f k = wkL (downR f) >>> exL (mapL getMu (funL init (wkL' k)))
  muR = mapR mu


-- Polarity shifts

instance Continuation r k => UpIntro k (Seq k) where
  upL   = mapL getUp
  upR   = mapR Up

instance Continuation r k => DownIntro k (Seq k) where
  downL = mapL getDown
  downR = mapR Down

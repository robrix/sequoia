{-# LANGUAGE TypeFamilies #-}
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
import           Data.Kind (Type)
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
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import qualified Sequoia.Value as V

-- Sequents

evalSeq :: K.Representable k => _Δ ~ KRep k => _Γ -|Seq k v|- _Δ -> k _Γ
evalSeq = evalC

newtype Seq k (v :: Type -> Type) _Γ _Δ = Seq { runSeq :: k _Δ -> k _Γ }
  deriving (Cat.Category, Profunctor) via C k
  deriving (Applicative, Functor, Monad) via C k _Γ

instance Representable k => ContPassing k (Seq k v) where
  inC = Seq
  exC = runSeq


liftLR :: ContPassing k c => c a b -> Seq k v (a < _Γ) (_Δ > b)
liftLR = dimap exl inr . Seq . exC


lowerLR :: ContPassing k c => (c a b -> _Γ -|Seq k v|- _Δ) -> a < _Γ -|Seq k v|- _Δ > b -> _Γ -|Seq k v|- _Δ
lowerLR f p = inC1' (\ _Δ _Γ -> _Δ ↓ f (inC1' (\ b a -> _Δ ↓ b ↓> p <↑ a • _Γ)) • _Γ)


-- Effectful sequents

runSeqT :: SeqT r s _Γ m _Δ -> ((_Δ -> m r) -> (_Γ -> m r))
runSeqT = dimap K runK . runSeq . getSeqT

newtype SeqT r s _Γ m _Δ = SeqT { getSeqT :: Seq (K (m r)) (V s) _Γ _Δ }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r s _Γ) where
  lift m = SeqT (inC1 (const . (m >>=)))


-- Core rules

instance (K.Representable k, V.Representable v) => Core k v (Seq k v) where
  f >>> g = f >>= pure <--> pushL g

  init = popL liftR


-- Structural rules

deriving via Contextually (Seq k v) instance (K.Representable k, V.Representable v) => Weaken   k v (Seq k v)
deriving via Contextually (Seq k v) instance (K.Representable k, V.Representable v) => Contract k v (Seq k v)
deriving via Contextually (Seq k v) instance (K.Representable k, V.Representable v) => Exchange k v (Seq k v)


-- Contextual rules

instance (K.Representable k, V.Representable v) => Contextual k v (Seq k v) where
  swapΓΔ f _Δ' _Γ' = inC1' (\ _Δ _Γ -> _Δ' ↓ f _Δ _Γ • _Γ')


-- Control

instance Control Seq where
  reset s = inC (•<< (evalSeq s •))
  shift s = inC1' (\ _Δ -> (inlK _Δ ↓ idK ↓> s <↑ inrK _Δ •))


-- Negation

instance (K.Representable k, V.Representable v) => NotIntro k v (Seq k v) where
  notL = notLK . kL
  notR = notRK . kR

instance (K.Representable k, V.Representable v) => NegateIntro k v (Seq k v) where
  negateL = negateLK . kL
  negateR = negateRK . kR


-- Additive

instance (K.Representable k, V.Representable v) => TopIntro k v (Seq k v) where
  topR = pure (inr Top)

instance (K.Representable k, V.Representable v) => ZeroIntro k v (Seq k v) where
  zeroL = liftL (inK absurdP)

instance (K.Representable k, V.Representable v) => WithIntro k v (Seq k v) where
  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = mapR2 inlr

instance (K.Representable k, V.Representable v) => SumIntro k v (Seq k v) where
  sumL a b = popL (pushL a <--> pushL b)
  sumR1 = mapR inl
  sumR2 = mapR inr


-- Multiplicative

instance (K.Representable k, V.Representable v) => BottomIntro k v (Seq k v) where
  botL = liftL (inK absurdN)
  botR = wkR

instance (K.Representable k, V.Representable v) => OneIntro k v (Seq k v) where
  oneL = wkL
  oneR = liftR One

instance (K.Representable k, V.Representable v) => ParIntro k v (Seq k v) where
  parL a b = popL (pushL a <--> pushL b)
  parR = fmap ((>>= inr . inl) <--> inr . inr)

instance (K.Representable k, V.Representable v) => TensorIntro k v (Seq k v) where
  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = mapR2 inlr


-- Logical biconditional/exclusive disjunction

instance (K.Representable k, V.Representable v) => IffIntro k v (Seq k v) where
  iffL1 s1 s2 = mapL getIff (withL1 (downR s1 ->⊢ s2))

  iffL2 s1 s2 = mapL getIff (withL2 (downR s1 ->⊢ s2))

  iffR s1 s2 = mapR Iff (funR (downL s1) ⊢& funR (downL s2))

instance (K.Representable k, V.Representable v) => XOrIntro k v (Seq k v) where
  xorL s1 s2 = mapL getXOr (subL (upR s1) ⊕⊢ subL (upR s2))

  xorR1 s1 s2 = mapR XOr (sumR1 (s1 ⊢-< upL s2))

  xorR2 s1 s2 = mapR XOr (sumR2 (s1 ⊢-< upL s2))


-- Implication

instance (K.Representable k, V.Representable v) => FunctionIntro k v (Seq k v) where
  funL a b = popL (\ f -> a >>> liftLR f >>> wkL' b)
  funR = lowerLR liftR . wkR'

instance (K.Representable k, V.Representable v) => SubtractionIntro k v (Seq k v) where
  subL f = mapL (sub <~) (tensorL (wkL' f >>> poppedL2 negateL init))
  subR a b = mapR (~> sub) (a ⊢⊗ negateR b)


-- Quantification

instance (K.Representable k, V.Representable v) => UniversalIntro k v (Seq k v) where
  forAllL p = mapL (notNegate . runForAll) p
  forAllR p = inC1' (\ _Δ _Γ -> inrK _Δ • ForAll (inK (\ k -> inlK _Δ ↓ k ↓> p • _Γ)))

instance (K.Representable k, V.Representable v) => ExistentialIntro k v (Seq k v) where
  existsL p = popL (dnE . runExists (pushL p))
  existsR p = mapR (Exists . liftDN) p


-- Recursion

instance (K.Representable k, V.Representable v) => NuIntro k v (Seq k v) where
  nuL = mapL runNu
  nuR s = wkR' s >>> existsL (mapL nu init)

instance (K.Representable k, V.Representable v) => MuIntro k v (Seq k v) where
  muL f k = wkL (downR f) >>> exL (mapL getMu (funL init (wkL' k)))
  muR = mapR mu


-- Polarity shifts

instance (K.Representable k, V.Representable v) => UpIntro k v (Seq k v) where
  upL   = mapL getUp
  upR   = mapR Up

instance (K.Representable k, V.Representable v) => DownIntro k v (Seq k v) where
  downL = mapL getDown
  downR = mapR Down

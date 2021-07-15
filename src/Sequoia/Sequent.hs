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
import           Control.Monad (ap)
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
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import           Sequoia.Profunctor.D (Dual(..), runControl, (•∘))
import           Sequoia.Value

-- Sequents

evalSeq :: _Γ -|Seq _Δ s|- _Δ -> K _Δ _Γ
evalSeq = evalC

newtype Seq r s _Γ _Δ = Seq { runSeq :: K r _Δ -> K r _Γ }

instance Functor (Seq r s a) where
  fmap = rmap

instance Applicative (Seq r s a) where
  pure a = Seq (inK . const . (• a))
  (<*>) = ap

instance Monad (Seq r s a) where
  Seq m >>= f = Seq (inK . \ b a -> m (inK (\ a' -> exC (f a') b • a)) • a)

instance Cat.Category (Seq r s) where
  id = Seq id
  Seq f . Seq g = Seq (g . f)

instance Profunctor (Seq r s) where
  dimap f g = Seq . dimap (contramap g) (contramap f) . runSeq

instance Monoid s => Dual r s (Seq r s) where
  inD f = Seq (inK . \ b a -> runControl (f (inV0 a) b) mempty)
  exD (Seq f) v k = f k •∘ v

  type R (Seq r s) = r
  type S (Seq r s) = s

instance ContPassing (K r) (Seq r s) where
  inC = Seq
  exC = runSeq


liftLR :: ContPassing (K r) c => c a b -> Seq r s (a < _Γ) (_Δ > b)
liftLR = dimap exl inr . Seq . exC


lowerLR :: ContPassing (K r) c => (c a b -> _Γ -|Seq r s|- _Δ) -> a < _Γ -|Seq r s|- _Δ > b -> _Γ -|Seq r s|- _Δ
lowerLR f p = inC1' (\ _Δ _Γ -> _Δ ↓ f (inC1' (\ b a -> _Δ ↓ b ↓> p <↑ a • _Γ)) • _Γ)


-- Effectful sequents

runSeqT :: SeqT r s _Γ m _Δ -> ((_Δ -> m r) -> (_Γ -> m r))
runSeqT = dimap K runK . runSeq . getSeqT

newtype SeqT r s _Γ m _Δ = SeqT { getSeqT :: Seq (m r) s _Γ _Δ }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r s _Γ) where
  lift m = SeqT (inC1 (const . (m >>=)))


-- Core rules

instance Core (K r) (V s) (Seq r s) where
  f >>> g = f >>= pure <--> pushL g

  init = popL liftR


-- Structural rules

deriving via Contextually (Seq r s) instance Weaken   (K r) (V s) (Seq r s)
deriving via Contextually (Seq r s) instance Contract (K r) (V s) (Seq r s)
deriving via Contextually (Seq r s) instance Exchange (K r) (V s) (Seq r s)


-- Contextual rules

instance Contextual (K r) (V s) (Seq r s) where
  swapΓΔ f _Δ' _Γ' = inC1' (\ _Δ _Γ -> _Δ' ↓ f _Δ _Γ • _Γ')


-- Control

instance Control K Seq where
  reset s = inC (•<< (evalSeq s •))
  shift s = inC1' (\ _Δ _Γ -> exC s (inlK _Δ |> idK) • (inrK _Δ <| _Γ))


-- Negation

instance NotIntro (K r) (V s) (Seq r s) where
  notL = notLK . kL
  notR = notRK . kR

instance NegateIntro (K r) (V s) (Seq r s) where
  negateL = negateLK . kL
  negateR = negateRK . kR


-- Additive

instance TopIntro (K r) (V s) (Seq r s) where
  topR = pure (inr Top)

instance ZeroIntro (K r) (V s) (Seq r s) where
  zeroL = liftL (inK absurdP)

instance WithIntro (K r) (V s) (Seq r s) where
  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = mapR2 inlr

instance SumIntro (K r) (V s) (Seq r s) where
  sumL a b = popL (pushL a <--> pushL b)
  sumR1 = mapR inl
  sumR2 = mapR inr


-- Multiplicative

instance BottomIntro (K r) (V s) (Seq r s) where
  botL = liftL (inK absurdN)
  botR = wkR

instance OneIntro (K r) (V s) (Seq r s) where
  oneL = wkL
  oneR = liftR One

instance ParIntro (K r) (V s) (Seq r s) where
  parL a b = popL (pushL a <--> pushL b)
  parR = fmap ((>>= inr . inl) <--> inr . inr)

instance TensorIntro (K r) (V s) (Seq r s) where
  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = mapR2 inlr


-- Logical biconditional/exclusive disjunction

instance IffIntro (K r) (V s) (Seq r s) where
  iffL1 s1 s2 = mapL getIff (withL1 (downR s1 ->⊢ s2))

  iffL2 s1 s2 = mapL getIff (withL2 (downR s1 ->⊢ s2))

  iffR s1 s2 = mapR Iff (funR (downL s1) ⊢& funR (downL s2))

instance XOrIntro (K r) (V s) (Seq r s) where
  xorL s1 s2 = mapL getXOr (subL (upR s1) ⊕⊢ subL (upR s2))

  xorR1 s1 s2 = mapR XOr (sumR1 (s1 ⊢-< upL s2))

  xorR2 s1 s2 = mapR XOr (sumR2 (s1 ⊢-< upL s2))


-- Implication

instance FunctionIntro (K r) (V s) (Seq r s) where
  funL a b = popL (\ f -> a >>> liftLR f >>> wkL' b)
  funR = lowerLR liftR . wkR'

instance SubtractionIntro (K r) (V s) (Seq r s) where
  subL f = mapL (sub <~) (tensorL (wkL' f >>> poppedL2 negateL init))
  subR a b = mapR (~> sub) (a ⊢⊗ negateR b)


-- Quantification

instance UniversalIntro (K r) (V s) (Seq r s) where
  forAllL p = mapL (notNegate . runForAll) p
  forAllR p = inC1' (\ _Δ _Γ -> inrK _Δ • ForAll (inK (\ k -> inlK _Δ ↓ k ↓> p • _Γ)))

instance ExistentialIntro (K r) (V s) (Seq r s) where
  existsL p = popL (dnE . runExists (pushL p))
  existsR p = mapR (Exists . liftDN) p


-- Recursion

instance NuIntro (K r) (V s) (Seq r s) where
  nuL = mapL runNu
  nuR s = wkR' s >>> existsL (mapL nu init)

instance MuIntro (K r) (V s) (Seq r s) where
  muL f k = wkL (downR f) >>> exL (mapL getMu (funL init (wkL' k)))
  muR = mapR mu


-- Polarity shifts

instance UpIntro (K r) (V s) (Seq r s) where
  upL   = mapL getUp
  upR   = mapR Up

instance DownIntro (K r) (V s) (Seq r s) where
  downL = mapL getDown
  downR = mapR Down

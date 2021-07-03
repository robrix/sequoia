{-# LANGUAGE TypeFamilies #-}
module Focalized.Sequent
( -- * Sequents
  runSeq
, evalSeq
, sequent
, dnESeq
, Seq(..)
, liftLR
, lowerLR
  -- * Effectful sequents
, runSeqT
, SeqT(..)
) where

import           Control.Applicative (liftA2)
import qualified Control.Category as Cat
import           Control.Monad.Trans.Class
import           Data.Functor.Contravariant
import           Data.Profunctor
import           Focalized.CPS
import           Focalized.Calculus.Additive
import           Focalized.Calculus.Context
import           Focalized.Calculus.Control
import           Focalized.Calculus.Core
import           Focalized.Calculus.Iff
import           Focalized.Calculus.Implicative
import           Focalized.Calculus.Mu
import           Focalized.Calculus.Multiplicative
import           Focalized.Calculus.Negation
import           Focalized.Calculus.Nu
import           Focalized.Calculus.Quantification
import           Focalized.Calculus.Shift
import           Focalized.Calculus.XOr
import           Focalized.Conjunction
import           Focalized.Continuation
import           Focalized.Disjunction
import           Prelude hiding (init)

-- Sequents

runSeq :: _Γ -|Seq k|- _Δ -> (k _Δ -> k _Γ)
runSeq = runCPS . getSeq

evalSeq :: Continuation k => _Δ ~ R k => _Γ -|Seq k|- _Δ -> k _Γ
evalSeq = (`runSeq` idK)

sequent :: (k _Δ -> k _Γ) -> _Γ -|Seq k|- _Δ
sequent = Seq . CPS

dnESeq :: Continuation k => k (k (_Γ -|Seq k|- _Δ)) -> _Γ -|Seq k|- _Δ
dnESeq = Seq . dnE . contramap (contramap getSeq)

newtype Seq k _Γ _Δ = Seq { getSeq :: _Γ -|CPS k|- _Δ }
  deriving (Applicative, Cat.Category, Functor, Monad, Profunctor)

liftLR :: Continuation k => CPS k a b -> Seq k (a < _Γ) (_Δ > b)
liftLR = Seq . dimap exl inr


lowerLR :: Continuation k => (a -|CPS k|- b -> _Γ -|Seq k|- _Δ) -> a < _Γ -|Seq k|- _Δ > b -> _Γ -|Seq k|- _Δ
lowerLR f p = sequent $ inK . \ k i -> exK (runSeq (f (CPS (\ kb -> runSeq p (k |> kb) •<< (<| i)))) k) i


-- Effectful sequents

runSeqT :: SeqT r _Γ m _Δ -> (m r •_Δ -> m r •_Γ)
runSeqT = runSeq . getSeqT

newtype SeqT r _Γ m _Δ = SeqT { getSeqT :: Seq ((•) (m r)) _Γ _Δ }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r _Γ) where
  lift m = SeqT (Seq (CPS (inK1 (const . (m >>=)))))


-- Core rules

instance Continuation k => Core (Seq k) where
  type K (Seq k) = k

  f >>> g = f >>= pure <--> pushL g

  init = popL liftR


-- Structural rules

deriving via Contextually (Seq k) instance Continuation k => Weaken   (Seq k)
deriving via Contextually (Seq k) instance Continuation k => Contract (Seq k)
deriving via Contextually (Seq k) instance Continuation k => Exchange (Seq k)


-- Contextual rules

instance Continuation k => Contextual (Seq k) where
  swapΓΔ f _Δ' _Γ' = sequent (inK . \ _Δ _Γ -> exK (runSeq (f _Δ _Γ) _Δ') _Γ')


-- Control

instance Control Seq where
  reset s = sequent (•<< exK (evalSeq s))
  shift p = sequent (\ k -> runSeq p (inlC k |> idK) •<< (inrC k <|))


-- Negation

instance Continuation k => NotIntro (Seq k) where
  notL = notLK . kL
  notR = notRK . kR

instance Continuation k => NegateIntro (Seq k) where
  negateL = negateLK . kL
  negateR = negateRK . kR


-- Additive

instance Continuation k => TopIntro (Seq k) where
  topR = pure (inr Top)

instance Continuation k => ZeroIntro (Seq k) where
  zeroL = liftL (inK absurdP)

instance Continuation k => WithIntro (Seq k) where
  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = liftA2 (liftA2 (-><-))

instance Continuation k => SumIntro (Seq k) where
  sumL a b = popL (pushL a <--> pushL b)
  sumR1 = mapR inl
  sumR2 = mapR inr


-- Multiplicative

instance Continuation k => BottomIntro (Seq k) where
  botL = liftL (inK absurdN)
  botR = wkR

instance Continuation k => OneIntro (Seq k) where
  oneL = wkL
  oneR = liftR One

instance Continuation k => ParIntro (Seq k) where
  parL a b = popL (pushL a <--> pushL b)
  parR = fmap ((>>= inr . inl) <--> inr . inr)

instance Continuation k => TensorIntro (Seq k) where
  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = liftA2 (liftA2 (-><-))


-- Logical biconditional/exclusive disjunction

instance Continuation k => IffIntro (Seq k) where
  iffL1 s1 s2 = mapL getIff (withL1 (downR s1 ->⊢ s2))

  iffL2 s1 s2 = mapL getIff (withL2 (downR s1 ->⊢ s2))

  iffR s1 s2 = mapR Iff (funR (downL s1) ⊢& funR (downL s2))

instance Continuation k => XOrIntro (Seq k) where
  xorL s1 s2 = mapL getXOr (subL (upR s1) ⊕⊢ subL (upR s2))

  xorR1 s1 s2 = mapR XOr (sumR1 (s1 ⊢-< upL s2))

  xorR2 s1 s2 = mapR XOr (sumR2 (s1 ⊢-< upL s2))


-- Implication

instance Continuation k => FunctionIntro (Seq k) where
  funL a b = popL (\ f -> a >>> liftLR (CPS (getFun f)) >>> wkL' b)
  funR = lowerLR (liftR . Fun . runCPS) . wkR'

instance Continuation k => SubtractionIntro (Seq k) where
  subL f = mapL getSub (tensorL (wkL' f >>> poppedL2 negateL init))
  subR a b = mapR Sub (a ⊢⊗ negateR b)


-- Quantification

instance Continuation k => UniversalIntro (Seq k) where
  forAllL p = mapL (notNegate . runForAll) p
  forAllR p = sequent (inK . \ k a -> exK (inrC k) (ForAll (inK ((`exK` a) . runSeq p . (inlC k |>)))))

instance Continuation k => ExistentialIntro (Seq k) where
  existsL p = popL (dnESeq . runExists (pushL p))
  existsR p = mapR (Exists . liftDN) p


-- Recursion

instance Continuation k => NuIntro (Seq k) where
  nuL = mapL runNu
  nuR s = wkR' s >>> existsL (mapL nu init)

instance Continuation k => MuIntro (Seq k) where
  muL f k = wkL (downR f) >>> exL (mapL getMu (funL init (wkL' k)))
  muR = mapR mu


-- Polarity shifts

instance Continuation k => UpIntro (Seq k) where
  upL   = mapL getUp
  upR   = mapR Up

instance Continuation k => DownIntro (Seq k) where
  downL = mapL getDown
  downR = mapR Down

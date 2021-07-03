{-# LANGUAGE TypeFamilies #-}
module Focalized.Sequent
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

evalSeq :: Continuation k => _Δ ~ R k => _Γ -|Seq k|- _Δ -> k _Γ
evalSeq = (`runSeq` idK)

newtype Seq k _Γ _Δ = Seq { runSeq :: k _Δ -> k _Γ }
  deriving (Cat.Category, Profunctor) via ViaCPS (Seq k)
  deriving (Applicative, Functor, Monad) via ViaCPS (Seq k) _Γ

instance Continuation k => CPS k (Seq k) where
  inC = Seq
  exC = runSeq


liftLR :: CPS k c => c a b -> Seq k (a < _Γ) (_Δ > b)
liftLR = dimap exl inr . Seq . exC


lowerLR :: CPS k c => (c a b -> _Γ -|Seq k|- _Δ) -> a < _Γ -|Seq k|- _Δ > b -> _Γ -|Seq k|- _Δ
lowerLR f p = Seq $ inK . \ k i -> exK (runSeq (f (inC (\ kb -> runSeq p (k |> kb) •<< (<| i)))) k) i


-- Effectful sequents

runSeqT :: SeqT r _Γ m _Δ -> (m r •_Δ -> m r •_Γ)
runSeqT = runSeq . getSeqT

newtype SeqT r _Γ m _Δ = SeqT { getSeqT :: Seq ((•) (m r)) _Γ _Δ }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r _Γ) where
  lift m = SeqT (Seq (inK1 (const . (m >>=))))


-- Core rules

instance Continuation k => Core k (Seq k) where
  f >>> g = f >>= pure <--> pushL g

  init = popL liftR


-- Structural rules

deriving via Contextually (Seq k) instance Continuation k => Weaken   k (Seq k)
deriving via Contextually (Seq k) instance Continuation k => Contract k (Seq k)
deriving via Contextually (Seq k) instance Continuation k => Exchange k (Seq k)


-- Contextual rules

instance Continuation k => Contextual k (Seq k) where
  swapΓΔ f _Δ' _Γ' = Seq (inK . \ _Δ _Γ -> exK (runSeq (f _Δ _Γ) _Δ') _Γ')


-- Control

instance Control Seq where
  reset s = Seq (•<< exK (evalSeq s))
  shift p = Seq (\ k -> runSeq p (inlC k |> idK) •<< (inrC k <|))


-- Negation

instance Continuation k => NotIntro k (Seq k) where
  notL = notLK . kL
  notR = notRK . kR

instance Continuation k => NegateIntro k (Seq k) where
  negateL = negateLK . kL
  negateR = negateRK . kR


-- Additive

instance Continuation k => TopIntro k (Seq k) where
  topR = pure (inr Top)

instance Continuation k => ZeroIntro k (Seq k) where
  zeroL = liftL (inK absurdP)

instance Continuation k => WithIntro k (Seq k) where
  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = mapR2 (-><-)

instance Continuation k => SumIntro k (Seq k) where
  sumL a b = popL (pushL a <--> pushL b)
  sumR1 = mapR inl
  sumR2 = mapR inr


-- Multiplicative

instance Continuation k => BottomIntro k (Seq k) where
  botL = liftL (inK absurdN)
  botR = wkR

instance Continuation k => OneIntro k (Seq k) where
  oneL = wkL
  oneR = liftR One

instance Continuation k => ParIntro k (Seq k) where
  parL a b = popL (pushL a <--> pushL b)
  parR = fmap ((>>= inr . inl) <--> inr . inr)

instance Continuation k => TensorIntro k (Seq k) where
  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = mapR2 (-><-)


-- Logical biconditional/exclusive disjunction

instance Continuation k => IffIntro k (Seq k) where
  iffL1 s1 s2 = mapL getIff (withL1 (downR s1 ->⊢ s2))

  iffL2 s1 s2 = mapL getIff (withL2 (downR s1 ->⊢ s2))

  iffR s1 s2 = mapR Iff (funR (downL s1) ⊢& funR (downL s2))

instance Continuation k => XOrIntro k (Seq k) where
  xorL s1 s2 = mapL getXOr (subL (upR s1) ⊕⊢ subL (upR s2))

  xorR1 s1 s2 = mapR XOr (sumR1 (s1 ⊢-< upL s2))

  xorR2 s1 s2 = mapR XOr (sumR2 (s1 ⊢-< upL s2))


-- Implication

instance Continuation k => FunctionIntro k (Seq k) where
  funL a b = popL (\ f -> a >>> liftLR f >>> wkL' b)
  funR = lowerLR liftR . wkR'

instance Continuation k => SubtractionIntro k (Seq k) where
  subL f = mapL getSub (tensorL (wkL' f >>> poppedL2 negateL init))
  subR a b = mapR Sub (a ⊢⊗ negateR b)


-- Quantification

instance Continuation k => UniversalIntro k (Seq k) where
  forAllL p = mapL (notNegate . runForAll) p
  forAllR p = Seq (inK . \ k a -> exK (inrC k) (ForAll (inK ((`exK` a) . runSeq p . (inlC k |>)))))

instance Continuation k => ExistentialIntro k (Seq k) where
  existsL p = popL (dnE . runExists (pushL p))
  existsR p = mapR (Exists . liftDN) p


-- Recursion

instance Continuation k => NuIntro k (Seq k) where
  nuL = mapL runNu
  nuR s = wkR' s >>> existsL (mapL nu init)

instance Continuation k => MuIntro k (Seq k) where
  muL f k = wkL (downR f) >>> exL (mapL getMu (funL init (wkL' k)))
  muR = mapR mu


-- Polarity shifts

instance Continuation k => UpIntro k (Seq k) where
  upL   = mapL getUp
  upR   = mapR Up

instance Continuation k => DownIntro k (Seq k) where
  downL = mapL getDown
  downR = mapR Down

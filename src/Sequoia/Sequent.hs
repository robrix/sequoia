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
import           Data.Profunctor
import           Prelude hiding (init)
import           Sequoia.Bijection
import           Sequoia.Calculus.Additive
import           Sequoia.Calculus.Context hiding ((<↑))
import           Sequoia.Calculus.Control as Calculus
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
import           Sequoia.Profunctor.D as D hiding ((>>>))
import           Sequoia.Value

-- Sequents

evalSeq :: _Γ -|Seq _Δ _Γ|- _Δ -> (_Γ -> _Δ)
evalSeq = evalD

newtype Seq r e _Γ _Δ = Seq { runSeq :: V e _Γ -> K r _Δ -> Context r e }
  deriving (Applicative, Functor, Monad) via (D r e _Γ)
  deriving (Cat.Category, Choice, Profunctor, Strong) via (D r e)

instance Dual r e (Seq r e) where
  inD = Seq
  exD = runSeq

  type R (Seq r e) = r
  type E (Seq r e) = e


liftLR :: D r e a b -> Seq r e (a < _Γ) (_Δ > b)
liftLR = dimap exl inr . coerceD

lowerLR :: (D r e a b -> _Γ -|Seq r e|- _Δ) -> a < _Γ -|Seq r e|- _Δ > b -> _Γ -|Seq r e|- _Δ
lowerLR f p = inD (\ _Γ _Δ -> exD (f (inD (\ a b -> exD p (a <| _Γ) (_Δ |> b)))) _Γ _Δ)


-- Effectful sequents

runSeqT :: SeqT r e _Γ m _Δ -> ((e -> _Γ) -> (_Δ -> m r) -> (e -> m r))
runSeqT = dimap V (dimap K runControl) . runSeq . getSeqT

newtype SeqT r s _Γ m _Δ = SeqT { getSeqT :: Seq (m r) s _Γ _Δ }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r s _Γ) where
  lift m = SeqT (inD (const (control . const . (m >>=) . (•))))


-- Core rules

instance Core r e (Seq r e) where
  f >>> g = f >>= pure <--> pushL g

  init = popL liftR


-- Structural rules

deriving via Contextually (Seq r e) instance Weaken   r e (Seq r e)
deriving via Contextually (Seq r e) instance Contract r e (Seq r e)
deriving via Contextually (Seq r e) instance Exchange r e (Seq r e)


-- Contextual rules

instance Contextual r e (Seq r e) where
  swapΓΔ f _Δ' _Γ' = inD (\ _Γ _Δ -> withVal (\ _Γ -> exD (f _Δ _Γ) (inV0 _Γ') _Δ') _Γ)

-- Control

instance Calculus.Control Seq where
  reset s = inD (\ _Γ _Δ -> control (exK _Δ . runControl (exD s _Γ idK)))
  shift s = inD (\ _Γ _Δ -> exD s (inV0 (inrK _Δ) <| _Γ) (inlK _Δ |> idK))


-- Negation

instance NotIntro r e (Seq r e) where
  notL = notLK . kL
  notR = notRK . kR

instance NegateIntro r e (Seq r e) where
  negateL = negateLK . kL
  negateR = negateRK . kR


-- Additive

instance TopIntro r e (Seq r e) where
  topR = pure (inr Top)

instance ZeroIntro r e (Seq r e) where
  zeroL = liftL (inK absurdP)

instance WithIntro r e (Seq r e) where
  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = mapR2 inlr

instance SumIntro r e (Seq r e) where
  sumL a b = popL (pushL a <--> pushL b)
  sumR1 = mapR inl
  sumR2 = mapR inr


-- Multiplicative

instance BottomIntro r e (Seq r e) where
  botL = liftL (inK absurdN)
  botR = wkR

instance OneIntro r e (Seq r e) where
  oneL = wkL
  oneR = liftR One

instance ParIntro r e (Seq r e) where
  parL a b = popL (pushL a <--> pushL b)
  parR = fmap ((>>= inr . inl) <--> inr . inr)

instance TensorIntro r e (Seq r e) where
  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = mapR2 inlr


-- Logical biconditional/exclusive disjunction

instance IffIntro r e (Seq r e) where
  iffL1 s1 s2 = mapL getIff (withL1 (downR s1 ->⊢ s2))

  iffL2 s1 s2 = mapL getIff (withL2 (downR s1 ->⊢ s2))

  iffR s1 s2 = mapR Iff (funR (downL s1) ⊢& funR (downL s2))

instance XOrIntro r e (Seq r e) where
  xorL s1 s2 = mapL getXOr (subL (upR s1) ⊕⊢ subL (upR s2))

  xorR1 s1 s2 = mapR XOr (sumR1 (s1 ⊢-< upL s2))

  xorR2 s1 s2 = mapR XOr (sumR2 (s1 ⊢-< upL s2))


-- Implication

instance FunctionIntro r e (Seq r e) where
  funL a b = popL (\ f -> a >>> liftLR (inDK (getFun f)) >>> wkL' b)
  funR = lowerLR (\ f -> inD (\ _ k -> inrK k •∘ (Fun <$> exDK f))) . wkR'

instance SubtractionIntro r e (Seq r e) where
  subL f = mapL (sub <~) (tensorL (wkL' f >>> poppedL2 negateL init))
  subR a b = mapR (~> sub) (a ⊢⊗ negateR b)


-- Quantification

instance UniversalIntro r e (Seq r e) where
  forAllL p = mapL (notNegate . runForAll) p
  forAllR p = inD (\ _Γ _Δ -> liftRunControlWith (\ run -> inrK _Δ •• ForAll (inK (\ k -> run (exD p _Γ (inlK _Δ |> k))))))

instance ExistentialIntro r e (Seq r e) where
  existsL p = popL (dnE . runExists (pushL p))
  existsR p = mapR (Exists . liftDN) p


-- Recursion

instance NuIntro r e (Seq r e) where
  nuL = mapL runNu
  nuR s = wkR' s >>> existsL (mapL nu init)

instance MuIntro r e (Seq r e) where
  muL f k = wkL (downR f) >>> exL (mapL getMu (funL init (wkL' k)))
  muR = mapR mu


-- Polarity shifts

instance UpIntro r e (Seq r e) where
  upL   = mapL getUp
  upR   = mapR Up

instance DownIntro r e (Seq r e) where
  downL = mapL getDown
  downR = mapR Down

module Sequoia.Sequent
( -- * Sequents
  evalSeq
, runSeq
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
import           Sequoia.Calculus.Context
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
import           Sequoia.Calculus.Structural
import           Sequoia.Calculus.XOr
import           Sequoia.Conjunction
import           Sequoia.Contextual
import           Sequoia.Continuation as K
import           Sequoia.Disjunction
import           Sequoia.Functor.K
import           Sequoia.Functor.V
import           Sequoia.Profunctor.ControlPassing as ControlPassing hiding ((>>>))
import           Sequoia.Value

-- Sequents

evalSeq :: _Γ -|Seq _Γ _Δ|- _Δ -> (_Γ -> _Δ)
evalSeq = evalCP

runSeq :: Seq e r _Γ _Δ -> ((e -> _Γ) -> (_Δ -> r) -> (e -> r))
runSeq s f g = evalSeq (dimap f g s)

newtype Seq e r _Γ _Δ = Seq { getSeq :: V e _Γ -> K r _Δ -> ControlPassing.Control e r }
  deriving (Env e, Res r) via (CP e r _Γ _Δ)
  deriving (Applicative, Functor, Monad) via (CP e r _Γ)
  deriving (Cat.Category, Choice, ControlPassing e r, Profunctor, Strong) via (CP e r)
  deriving (LocalEnv2) via CP


liftLR :: ControlPassing e r d => d a b -> Seq e r (a < _Γ) (_Δ > b)
liftLR = dimap exl inr . coerceCP

lowerLR :: ControlPassing e r d => (d a b -> _Γ -|Seq e r|- _Δ) -> a < _Γ -|Seq e r|- _Δ > b -> _Γ -|Seq e r|- _Δ
lowerLR f p = inCP (\ _Γ _Δ -> exCP (f (inCP (\ a b -> exCP p (a <| _Γ) (_Δ |> b)))) _Γ _Δ)


-- Effectful sequents

runSeqT :: SeqT e r _Γ m _Δ -> ((e -> _Γ) -> (_Δ -> m r) -> (e -> m r))
runSeqT = runSeq . getSeqT

newtype SeqT e r _Γ m _Δ = SeqT { getSeqT :: Seq e (m r) _Γ _Δ }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r s _Γ) where
  lift m = SeqT (inCP (const (Control . const . (m >>=) . (•))))


-- Core rules

instance Core e r (Seq e r) where
  f >>> g = f >>= pure <--> pushL g

  init = popL liftR


-- Structural rules

deriving via Contextually (Seq e r) instance Weaken   e r (Seq e r)
deriving via Contextually (Seq e r) instance Contract e r (Seq e r)
deriving via Contextually (Seq e r) instance Exchange e r (Seq e r)


-- Contextual rules

instance Contextual e r (Seq e r) where
  swapΓΔ f _Γ' _Δ' = inCP (\ _Γ _Δ -> exCP (f _Γ _Δ) _Γ' _Δ')


-- Control

instance Calculus.Control Seq where
  reset s = inCP (\ _Γ _Δ -> Control (exK _Δ . getControl (exCP s _Γ idK)))
  shift s = inCP (\ _Γ _Δ -> exCP s (inV0 (inrK _Δ) <| _Γ) (inlK _Δ |> idK))


-- Negation

instance NotIntro e r (Seq e r) where
  notL = notLK . kL
  notR = notRK . kR

instance NegateIntro e r (Seq e r) where
  negateL = negateLK . kL
  negateR = negateRK . kR


-- Additive

instance TopIntro e r (Seq e r) where
  topR = pure (inr Top)

instance ZeroIntro e r (Seq e r) where
  zeroL = liftL (inK absurdP)

instance WithIntro e r (Seq e r) where
  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = mapR2 inlr

instance SumIntro e r (Seq e r) where
  sumL a b = popL (pushL a <--> pushL b)
  sumR1 = mapR inl
  sumR2 = mapR inr


-- Multiplicative

instance BottomIntro (Seq e r) where
  botL = liftL (inK absurdN)
  botR = wkR

instance OneIntro e r (Seq e r) where
  oneL = wkL
  oneR = liftR One

instance ParIntro e r (Seq e r) where
  parL a b = popL (pushL a <--> pushL b)
  parR = fmap ((>>= inr . inl) <--> inr . inr)

instance TensorIntro e r (Seq e r) where
  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = mapR2 inlr


-- Logical biconditional/exclusive disjunction

instance IffIntro e r (Seq e r) where
  iffL1 s1 s2 = mapL getIff (withL1 (downR s1 ->⊢ s2))

  iffL2 s1 s2 = mapL getIff (withL2 (downR s1 ->⊢ s2))

  iffR s1 s2 = mapR Iff (funR (downL s1) ⊢& funR (downL s2))

instance XOrIntro e r (Seq e r) where
  xorL s1 s2 = mapL getXOr (subL (upR s1) ⊕⊢ subL (upR s2))

  xorR1 s1 s2 = mapR XOr (sumR1 (s1 ⊢-< upL s2))

  xorR2 s1 s2 = mapR XOr (sumR2 (s1 ⊢-< upL s2))


-- Implication

instance FunctionIntro e r (Seq e r) where
  funL a b = popL (\ f -> a >>> liftLR f >>> wkL' b)
  funR = lowerLR liftR . wkR'

instance SubtractionIntro e r (Seq e r) where
  subL f = mapL (sub <~) (tensorL (wkL' f >>> poppedL2 negateL init))
  subR a b = mapR (~> sub) (a ⊢⊗ negateR b)


-- Quantification

instance UniversalIntro e r (Seq e r) where
  forAllL p = mapL (notNegate . runForAll) p
  forAllR p = inCP (\ _Γ _Δ -> liftRes (\ run -> inrK _Δ •• ForAll (inK (\ k -> run (exCP p _Γ (inlK _Δ |> k))))))

instance ExistentialIntro e r (Seq e r) where
  existsL p = popL (dnE . runExists (pushL p))
  existsR p = mapR (Exists . liftDN) p


-- Recursion

instance NuIntro e r (Seq e r) where
  nuL = mapL runNu
  nuR s = wkR' s >>> existsL (mapL nu init)

instance MuIntro e r (Seq e r) where
  muL f k = wkL (downR f) >>> exL (mapL getMu (funL init (wkL' k)))
  muR = mapR mu


-- Polarity shifts

instance UpIntro e r (Seq e r) where
  upL   = mapL getUp
  upR   = mapR Up

instance DownIntro e r (Seq e r) where
  downL = mapL getDown
  downR = mapR Down

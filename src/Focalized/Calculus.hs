{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus
( -- * Sequents
  runSeq
, evalSeq
, Seq(..)
, liftLR
, lowerLR
  -- * Effectful sequents
, runSeqT
, SeqT(..)
  -- * Contexts
, module Focalized.Calculus.Context
  -- * Core rules
, module Focalized.Calculus.Core
  -- * Control
, Control(..)
  -- * Negation
, Negation
, type (¬)(..)
, type (¬-)
, NegNegation(..)
, type (-)(..)
, type (-¬)
, PosNegation(..)
  -- * Additive
, Additive
, Top(..)
, AdditiveTruth(..)
, Zero
, AdditiveFalsity(..)
, type (&)(..)
, AdditiveConj(..)
, type (⊕)(..)
, AdditiveDisj(..)
  -- * Multiplicative
, Multiplicative
, Bot
, MultiplicativeFalsity(..)
, One(..)
, MultiplicativeTruth(..)
, type (⅋)(..)
, MultiplicativeDisj(..)
, type (⊗)(..)
, MultiplicativeConj(..)
  -- * Implicative
, runFun
, appFun
, appFun2
, liftFun
, liftFun'
, Fun(..)
, type (~>)
, type (~~)
, Implicative(..)
, Sub(..)
, type (-<)
, type (~-)
, Coimplicative(..)
  -- * Quantifying
, Quantifying
, ForAll(..)
, Universal(..)
, Exists(..)
, Existential(..)
  -- * Recursive
, Nu(..)
, NuF(..)
, Corecursive(..)
, Mu(..)
, MuF(..)
, foldMu
, unfoldMu
, refoldMu
, refold
, Recursive(..)
  -- * Polarity
, N(..)
, P(..)
  -- * Polarity shifts
, Polarized
, Neg
, Pos
, Shifting
, Up(..)
, ShiftingN(..)
, Down(..)
, ShiftingP(..)
) where

import           Control.Applicative (liftA2)
import qualified Control.Category as Cat
import           Control.Monad.Trans.Class
import           Data.Functor.Contravariant (contramap)
import           Data.Functor.Identity
import           Data.Kind (Constraint)
import           Data.Profunctor
import           Focalized.CPS
import           Focalized.Calculus.Context
import           Focalized.Calculus.Control
import           Focalized.Calculus.Core
import           Focalized.Calculus.Negation
import           Focalized.Connective
import           Focalized.Polarity
import           Prelude hiding (init)

-- Sequents

runSeq :: Seq r i o -> ((o -> r) -> (i -> r))
runSeq = runCPS . getSeq

evalSeq :: Seq o i o -> (i -> o)
evalSeq = (`runSeq` id)

sequent :: ((o -> r) -> (i -> r)) -> Seq r i o
sequent = Seq . CPS

newtype Seq r i o = Seq { getSeq :: CPS r i o }
  deriving (Applicative, Cat.Category, Functor, Monad, Profunctor)

liftLR :: CPS r a b -> Seq r (a < i) (o > b)
liftLR = Seq . dimap exl inr


lowerLR :: (CPS r a b -> Seq r i o) -> Seq r (a < i) (o > b) -> Seq r i o
lowerLR f p = sequent $ \ k i -> runSeq (f (CPS (\ kb a -> runSeq p (k |> kb) (a <| i)))) k i


-- Effectful sequents

runSeqT :: SeqT r i m o -> ((o -> m r) -> (i -> m r))
runSeqT = runSeq . getSeqT

newtype SeqT r i m o = SeqT { getSeqT :: Seq (m r) i o }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r i) where
  lift m = SeqT (Seq (CPS (\ k _ -> m >>= k)))


-- Core rules

instance Core Seq where
  f >>> g = f >>= pure |> pushL g

  init = popL liftR


-- Structural rules

instance Weaken Seq where
instance Contract Seq where
instance Exchange Seq where


-- Contextual rules

instance Contextual Seq where
  popL f = sequent $ \ k -> uncurryConj ((`runSeq` k) . f)
  pushL s a = sequent $ \ k -> runSeq s k . (a <|)

  popR f = sequent $ \ k -> runSeq (f (K (k . inr))) (k . inl)
  pushR s a = sequent $ \ k -> runSeq s (k |> runK a)


-- Control

instance Control Seq where
  reset s = sequent (. evalSeq s)
  shift p = sequent (\ k -> runSeq p (k . inl |> id) . (K (k . inr) <|))


-- Negation

instance NegNegation Seq where
  notL = notLK . kL
  notR = notRK . kR

instance PosNegation Seq where
  negateL = negateLK . kL
  negateR = negateRK . kR


-- Additive

type Additive s = (AdditiveTruth s, AdditiveFalsity s, AdditiveConj s, AdditiveDisj s)


data Top = Top
  deriving (Eq, Ord, Show)

instance Polarized N Top where


class AdditiveTruth s where
  topR
    -- -----------------
    :: i -|s r|- o > Top
  default topR
    :: Contextual s
    -- -----------------
    => i -|s r|- o > Top
  topR = liftR Top

instance AdditiveTruth Seq where


data Zero

instance Polarized P Zero where

absurdP :: Zero -> a
absurdP = \case


class AdditiveFalsity s where
  zeroL
    -- ------------------
    :: Zero < i -|s r|- o
  default zeroL
    :: Contextual s
    -- ------------------
    => Zero < i -|s r|- o
  zeroL = popL absurdP

instance AdditiveFalsity Seq where


newtype a & b = With (forall r . (a -> b -> r) -> r)
  deriving (Functor)

infixr 6 &

instance (Neg a, Neg b) => Polarized N (a & b) where

instance Foldable ((&) f) where
  foldMap = foldMapConj

instance Traversable ((&) f) where
  traverse = traverseConj

instance Conj (&) where
  inlr a b = With $ \ f -> f a b
  exl (With run) = run const
  exr (With run) = run (const id)


class (Core s, Structural s, Negation s) => AdditiveConj s where
  {-# MINIMAL (withL1, withL2 | withLSum), withR #-}
  withL1
    :: (Neg a, Neg b)
    => a     < i -|s r|- o
    -- -------------------
    -> a & b < i -|s r|- o
  default withL1
    :: (Neg a, Neg b, AdditiveDisj s)
    => a     < i -|s r|- o
    -- -------------------
    -> a & b < i -|s r|- o
  withL1 = withLSum . sumR1 . negateR
  withL2
    :: (Neg a, Neg b)
    =>     b < i -|s r|- o
    -- -------------------
    -> a & b < i -|s r|- o
  default withL2
    :: (Neg a, Neg b, AdditiveDisj s)
    =>     b < i -|s r|- o
    -- -------------------
    -> a & b < i -|s r|- o
  withL2 = withLSum . sumR2 . negateR
  withLSum
    :: (Neg a, Neg b)
    =>         i -|s r|- o > r -a ⊕ r -b
    -- ---------------------------------
    -> a & b < i -|s r|- o
  default withLSum
    :: (Neg a, Neg b, AdditiveDisj s)
    =>         i -|s r|- o > r -a ⊕ r -b
    -- ---------------------------------
    -> a & b < i -|s r|- o
  withLSum p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))
  withR
    :: (Neg a, Neg b)
    => i -|s r|- o > a   ->   i -|s r|- o > b
    -- --------------------------------------
    ->           i -|s r|- o > a & b
  withR1'
    :: (Neg a, Neg b)
    => i -|s r|- o > a & b
    -- -------------------
    -> i -|s r|- o > a
  withR1' t = wkR' t >>> withL1 init
  withR2'
    :: (Neg a, Neg b)
    => i -|s r|- o > a & b
    -- -------------------
    -> i -|s r|- o > b
  withR2' t = wkR' t >>> withL2 init

instance AdditiveConj Seq where
  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  withR = liftA2 (liftA2 inlr)


data a ⊕ b
  = InL !a
  | InR !b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 ⊕

instance (Pos a, Pos b) => Polarized P (a ⊕ b)

instance Disj (⊕) where
  inl = InL
  inr = InR
  exlr ifl ifr = \case
    InL l -> ifl l
    InR r -> ifr r


class (Core s, Structural s, Negation s) => AdditiveDisj s where
  {-# MINIMAL (sumL | sumLWith), sumR1, sumR2 #-}
  sumL
    :: (Pos a, Pos b)
    => a < i -|s r|- o   ->   b < i -|s r|- o
    -- --------------------------------------
    ->           a ⊕ b < i -|s r|- o
  default sumL
    :: (Pos a, Pos b, AdditiveConj s)
    => a < i -|s r|- o   ->   b < i -|s r|- o
    -- --------------------------------------
    ->           a ⊕ b < i -|s r|- o
  sumL p1 p2 = sumLWith (withR (notR p1) (notR p2))
  sumL1'
    :: (Pos a, Pos b)
    => a ⊕ b < i -|s r|- o
    -- -------------------
    -> a     < i -|s r|- o
  sumL1' p = sumR1 init >>> wkL' p
  sumL2'
    :: (Pos a, Pos b)
    => a ⊕ b < i -|s r|- o
    -- -------------------
    ->     b < i -|s r|- o
  sumL2' p = sumR2 init >>> wkL' p
  sumLWith
    :: (Pos a, Pos b)
    =>         i -|s r|- o > r ¬a & r ¬b
    -- ---------------------------------
    -> a ⊕ b < i -|s r|- o
  default sumLWith
    :: (Pos a, Pos b, AdditiveConj s)
    =>         i -|s r|- o > r ¬a & r ¬b
    -- ---------------------------------
    -> a ⊕ b < i -|s r|- o
  sumLWith p = sumL (wkL p >>> withL1 (notL init)) (wkL p >>> withL2 (notL init))
  sumR1
    :: (Pos a, Pos b)
    => i -|s r|- o > a
    -- -------------------
    -> i -|s r|- o > a ⊕ b
  sumR2
    :: (Pos a, Pos b)
    => i -|s r|- o >     b
    -- -------------------
    -> i -|s r|- o > a ⊕ b

instance AdditiveDisj Seq where
  sumL a b = popL (exlr (pushL a) (pushL b))
  sumR1 = mapR inl
  sumR2 = mapR inr


-- Multiplicative

type Multiplicative s = (MultiplicativeFalsity s, MultiplicativeTruth s, MultiplicativeDisj s, MultiplicativeConj s)


data Bot

instance Polarized N Bot where

absurdN :: Bot -> a
absurdN = \case


class (Core s, Contextual s, Structural s, Negation s) => MultiplicativeFalsity s where
  botL
    -- -----------------
    :: Bot < i -|s r|- o
  botL = liftL (K absurdN)
  botR
    :: i -|s r|- o
    -- -----------------
    -> i -|s r|- o > Bot
  botR = wkR
  botR'
    :: i -|s r|- o > Bot
    -- -----------------
    -> i -|s r|- o
  botR' = (>>> botL)

instance MultiplicativeFalsity Seq where


data One = One
  deriving (Eq, Ord, Show)

instance Polarized P One where


class (Core s, Contextual s, Structural s, Negation s) => MultiplicativeTruth s where
  oneL
    :: i -|s r|- o
    -- -----------------
    -> One < i -|s r|- o
  oneL = wkL
  oneL'
    :: One < i -|s r|- o
    -- -----------------
    -> i -|s r|- o
  oneL' = (oneR >>>)
  oneR
    -- -----------------
    :: i -|s r|- o > One
  oneR = liftR One

instance MultiplicativeTruth Seq where


newtype a ⅋ b = Par (forall r . (a -> r) -> (b -> r) -> r)
  deriving (Functor)

infixr 7 ⅋

instance (Neg a, Neg b) => Polarized N (a ⅋ b) where

instance Foldable ((⅋) f) where
  foldMap = foldMapDisj

instance Traversable ((⅋) f) where
  traverse = traverseDisj

instance Disj (⅋) where
  inl l = Par $ \ ifl _ -> ifl l
  inr r = Par $ \ _ ifr -> ifr r
  exlr ifl ifr (Par run) = run ifl ifr


class (Core s, Structural s, Negation s, Contextual s) => MultiplicativeDisj s where
  {-# MINIMAL (parL | parLTensor), parR #-}
  parL
    :: (Neg a, Neg b)
    => a < i -|s r|- o   ->   b < i -|s r|- o
    -- --------------------------------------
    ->          a ⅋ b < i -|s r|- o
  default parL
    :: (Neg a, Neg b, MultiplicativeConj s)
    => a < i -|s r|- o   ->   b < i -|s r|- o
    -- --------------------------------------
    ->          a ⅋ b < i -|s r|- o
  parL p1 p2 = parLTensor (tensorR (negateR p1) (negateR p2))
  parLTensor
    :: (Neg a, Neg b)
    =>         i -|s r|- o > r -a ⊗ r -b
    -- ---------------------------------
    -> a ⅋ b < i -|s r|- o
  default parLTensor
    :: (Neg a, Neg b, MultiplicativeConj s)
    =>         i -|s r|- o > r -a ⊗ r -b
    -- ---------------------------------
    -> a ⅋ b < i -|s r|- o
  parLTensor p = wkL p >>> tensorL (negateL (negateL (parL (wkR init) init)))
  parR
    :: (Neg a, Neg b)
    => i -|s r|- o > a > b
    -- -------------------
    -> i -|s r|- o > a ⅋ b
  parR'
    :: (Neg a, Neg b)
    => i -|s r|- o > a ⅋ b
    -- -------------------
    -> i -|s r|- o > a > b
  parR' p = poppedR (wkR . wkR) p >>> parL (wkR init) init

instance MultiplicativeDisj Seq where
  parL a b = popL (exlr (pushL a) (pushL b))
  parR ab = (>>= inr . inl) |> inr . inr <$> ab


data a ⊗ b = !a :⊗ !b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 ⊗, :⊗

instance (Pos a, Pos b) => Polarized P (a ⊗ b) where

instance Conj (⊗) where
  inlr = (:⊗)
  exl (l :⊗ _) = l
  exr (_ :⊗ r) = r


class (Core s, Structural s, Negation s, Contextual s) => MultiplicativeConj s where
  {-# MINIMAL (tensorL | tensorLPar), tensorR #-}
  tensorL
    :: (Pos a, Pos b)
    => a < b < i -|s r|- o
    -- -------------------
    -> a ⊗ b < i -|s r|- o
  default tensorL
    :: (Pos a, Pos b, MultiplicativeDisj s)
    => a < b < i -|s r|- o
    -- -------------------
    -> a ⊗ b < i -|s r|- o
  tensorL = tensorLPar . parR . notR . notR
  tensorLPar
    :: (Pos a, Pos b)
    =>         i -|s r|- o > r ¬a ⅋ r ¬b
    -- ---------------------------------
    -> a ⊗ b < i -|s r|- o
  default tensorLPar
    :: (Pos a, Pos b, MultiplicativeDisj s)
    =>         i -|s r|- o > r ¬a ⅋ r ¬b
    -- ---------------------------------
    -> a ⊗ b < i -|s r|- o
  tensorLPar p = wkL p >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
  tensorL'
    :: (Pos a, Pos b)
    => a ⊗ b < i -|s r|- o
    -- -------------------
    -> a < b < i -|s r|- o
  tensorL' p = tensorR init (wkL init) >>> popL (wkL . wkL . pushL p)
  tensorR
    :: (Pos a, Pos b)
    => i -|s r|- o > a   ->   i -|s r|- o > b
    -- --------------------------------------
    ->          i -|s r|- o > a ⊗ b

instance MultiplicativeConj Seq where
  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = liftA2 (liftA2 inlr)


-- Implicative

runFun :: (a ~~r~> b) -> Seq r (a < i) (o > b)
runFun = Seq . dimap exl inr . getFun

appFun :: (a ~~r~> b) -> a -> (b -> r) -> r
appFun = appCPS . getFun

appFun2 :: (a ~~r~> b ~~r~> c) -> a -> b -> (c -> r) -> r
appFun2 = appCPS2 . fmap getFun . getFun

liftFun :: ((b -> r) -> (a -> r)) -> a ~~r~> b
liftFun = Fun . CPS

liftFun' :: (a -> (b -> r) -> r) -> a ~~r~> b
liftFun' = liftFun . flip

newtype Fun r a b = Fun { getFun :: CPS r a b }

instance (Pos a, Neg b) => Polarized N (Fun r a b) where

type a ~~ r = Fun r a
type f ~> b = f b

infixr 6 ~~
infixr 5 ~>


class (Core s, Structural s, Negation s) => Implicative s where
  {-# MINIMAL (funL | funLSub), funR #-}
  funL
    :: (Pos a, Neg b)
    => i -|s r|- o > a   ->   b < i -|s r|- o
    -- --------------------------------------
    ->        a ~~r~> b < i -|s r|- o
  default funL
    :: (Pos a, Neg b, Coimplicative s)
    => i -|s r|- o > a   ->   b < i -|s r|- o
    -- --------------------------------------
    ->        a ~~r~> b < i -|s r|- o
  funL pa pb = funLSub (subR pa pb)
  funLSub
    :: (Pos a, Neg b)
    =>             i -|s r|- o > a ~-r-< b
    -- -----------------------------------
    -> a ~~r~> b < i -|s r|- o
  default funLSub
    :: (Pos a, Neg b, Coimplicative s)
    =>             i -|s r|- o > a ~-r-< b
    -- -----------------------------------
    -> a ~~r~> b < i -|s r|- o
  funLSub p = wkL p >>> subL (exL (funL init init))
  funL2
    :: (Pos a, Neg b)
    -- -------------------------------
    => a ~~r~> b < a < i -|s r|- o > b
  funL2 = funL init init
  funR
    :: (Pos a, Neg b)
    => a < i -|s r|- o > b
    -- ---------------------------
    ->     i -|s r|- o > a ~~r~> b
  ($$)
    :: (Pos a, Neg b)
    => i -|s r|- o > a ~~r~> b   ->   i -|s r|- o > a
    -- ----------------------------------------------
    ->                i -|s r|- o > b
  f $$ a = wkR' f >>> wkR' a `funL` init
  funR'
    :: (Pos a, Neg b)
    =>     i -|s r|- o > a ~~r~> b
    -- ---------------------------
    -> a < i -|s r|- o > b
  funR' p = wkL (wkR' p) >>> funL2

instance Implicative Seq where
  funL a b = popL (\ f -> a >>> runFun f >>> wkL' b)
  funR = lowerLR (liftR . Fun) . wkR'


data Sub r a b = Sub { subA :: !a, subK :: !(r -b) }

instance (Pos a, Neg b) => Polarized P (Sub r a b) where

type a ~-r = Sub r a
type r-< b = r b

infixr 6 ~-
infixr 5 -<


class (Core s, Structural s, Negation s) => Coimplicative s where
  {-# MINIMAL (subL | subLFun), subR #-}
  subL
    :: (Pos a, Neg b)
    =>         a < i -|s r|- o > b
    -- ---------------------------
    -> a ~-r-< b < i -|s r|- o
  default subL
    :: (Pos a, Neg b, Implicative s)
    =>         a < i -|s r|- o > b
    -- ---------------------------
    -> a ~-r-< b < i -|s r|- o
  subL = subLFun . funR
  subLFun
    :: (Pos a, Neg b)
    =>             i -|s r|- o > a ~~r~> b
    -- -----------------------------------
    -> a ~-r-< b < i -|s r|- o
  default subLFun
    :: (Pos a, Neg b, Implicative s)
    =>             i -|s r|- o > a ~~r~> b
    -- -----------------------------------
    -> a ~-r-< b < i -|s r|- o
  subLFun p = wkL p >>> exL (subL (exL (funL init init)))
  subL'
    :: (Pos a, Neg b)
    => a ~-r-< b < i -|s r|- o
    -- ---------------------------
    ->         a < i -|s r|- o > b
  subL' p = subR init init >>> wkR (wkL' p)
  subR
    :: (Pos a, Neg b)
    => i -|s r|- o > a   ->   b < i -|s r|- o
    -- --------------------------------------
    ->        i -|s r|- o > a ~-r-< b

instance Coimplicative Seq where
  subL b = popL (\ s -> liftR (subA s) >>> b >>> liftL (getNegate (subK s)))
  subR a b = liftA2 Sub <$> a <*> negateR b


-- Quantifying

type Quantifying s = (Universal s, Existential s)


newtype ForAll r p f = ForAll { runForAll :: forall x . Polarized p x => r ••f x }

instance Polarized N (ForAll r p f)


class (Core s, Structural s, Negation s, Contextual s, Shifting s) => Universal s where
  {-# MINIMAL (forAllL | forAllLExists), forAllR #-}
  forAllL
    :: (Polarized n x, Neg (f x))
    =>        r ¬-f x < i -|s r|- o
    -- ----------------------------
    -> ForAll r n f   < i -|s r|- o
  default forAllL
    :: (Polarized n x, ForAllC (Polarized n) Neg f, Existential s)
    =>        r ¬-f x < i -|s r|- o
    -- ----------------------------
    -> ForAll r n f   < i -|s r|- o
  forAllL p = forAllLExists (existsR (mapR C (notL' p)))
  forAllLExists
    :: ForAllC (Polarized n) Neg f
    =>                i -|s r|- o > Exists r n ((-) r · f)
    -- ---------------------------------------------------
    -> ForAll r n f < i -|s r|- o
  default forAllLExists
    :: (ForAllC (Polarized n) Neg f, Existential s)
    =>                i -|s r|- o > Exists r n ((-) r · f)
    -- ---------------------------------------
    -> ForAll r n f < i -|s r|- o
  forAllLExists p = wkL p >>> existsL (mapL getC (negateL (forAllL (notL (negateR init)))))
  forAllR
    :: ForAllC (Polarized n) Neg f
    => (forall x . Polarized n x => i -|s r|- o >            f x)
    -- ---------------------------------------
    ->                              i -|s r|- o > ForAll r n f
  forAllR'
    :: ForAllC (Polarized n) Neg f
    =>                              i -|s r|- o > ForAll r n f
    -- ---------------------------------------
    -> (forall x . Polarized n x => i -|s r|- o >            f x)
  forAllR' p = wkR' p >>> forAllL (dneN init)

instance Universal Seq where
  forAllL p = mapL (notNegate . runForAll) p
  forAllR p = sequent $ \ k a -> k (inr (ForAll (K (\ k' -> runSeq p (k . inl |> runK k') a))))


data Exists r p f = forall x . Polarized p x => Exists (r ••f x)

instance Polarized P (Exists r p f)

runExists :: (forall x . Polarized p x => f x -> a) -> Exists r p f -> r ••a
runExists f (Exists r) = K (\ k -> runK r (K (runK k . f)))


class (Core s, Structural s, Negation s, Contextual s, Shifting s) => Existential s where
  {-# MINIMAL (existsL | existsLForAll), existsR #-}
  existsL
    :: (forall x . Polarized n x => f x < i -|s r|- o)
    -- -----------------------------------------------
    ->                   Exists r n f   < i -|s r|- o
  default existsL
    :: (ForAllC (Polarized n) Pos f, Universal s)
    => (forall x . Polarized n x => f x < i -|s r|- o)
    -- -----------------------------------------------
    ->                   Exists r n f   < i -|s r|- o
  existsL s = existsLForAll (forAllR (mapR C (notR s)))
  existsL'
    :: ForAllC (Polarized n) Pos f
    =>                   Exists r n f   < i -|s r|- o
    -- -----------------------------------------------
    -> (forall x . Polarized n x => f x < i -|s r|- o)
  existsL' p = existsR init >>> wkL' p
  existsLForAll
    :: ForAllC (Polarized n) Pos f
    =>                i -|s r|- o > ForAll r n ((¬) r · f)
    -- ---------------------------------------------------
    -> Exists r n f < i -|s r|- o
  default existsLForAll
    :: (ForAllC (Polarized n) Pos f, Universal s)
    =>                i -|s r|- o > ForAll r n ((¬) r · f)
    -- ---------------------------------------------------
    -> Exists r n f < i -|s r|- o
  existsLForAll p = wkL p >>> exL (existsL (exL (forAllL (notL (negateR (mapL getC (notL init)))))))
  existsR
    :: (Polarized n x, Pos (f x))
    => i -|s r|- o >            f x
    -- ----------------------------
    -> i -|s r|- o > Exists r n f

instance Existential Seq where
  existsL p = popL (dnESeq . runExists (pushL p))
  existsR p = mapR (Exists . dnI) p


-- Recursive

data Nu r f = forall x . Pos x => Nu { getNu :: Down (x ~~r~> f x) ⊗ x }

instance Polarized N (Nu r f) where

newtype NuF r f a = NuF { getNuF :: Down (a ~~r~> f a) ⊗ a }

instance (Neg (f a), Pos a) => Polarized P (NuF r f a)

nu :: Pos x => NuF r f x -> Nu r f
nu r = Nu (getNuF r)

runNu :: Nu r f -> Exists r P (NuF r f)
runNu (Nu r) = Exists (dnI (NuF r))


class (Core s, Structural s, Implicative s) => Corecursive s where
  nuL
    :: ForAllC Pos Neg f
    => Exists r P (NuF r f) < i -|s r|- o
    -- ----------------------------------
    ->             Nu  r f  < i -|s r|- o
  nuR
    :: ForAllC Pos Neg f
    => i -|s r|- o > Exists r P (NuF r f)
    -- ----------------------------------
    -> i -|s r|- o >             Nu  r f
  nuR'
    :: ForAllC Pos Neg f
    => i -|s r|- o >             Nu  r f
    -- ----------------------------------
    -> i -|s r|- o > Exists r P (NuF r f)
  nuR' p = wkR' p >>> nuL init

instance Corecursive Seq where
  nuL = mapL runNu
  nuR s = wkR' s >>> existsL (mapL nu init)


newtype Mu r f = Mu { getMu :: forall x . Neg x => Down (FAlg r f x) ~~r~> x }

type FAlg r f x = f x ~~r~> x

instance Polarized N (Mu r f) where

newtype MuF r f a = MuF { getMuF :: Down (FAlg r f a) ~~r~> a }

instance (Pos (f a), Neg a) => Polarized N (MuF r f a) where

mu :: ForAll r N (MuF r f) -> Mu r f
mu r = Mu (dnEFun (contramap (contramap getMuF) (runForAll r)))

foldMu :: Neg a => CPS r (f a) a -> CPS r (Mu r f) a
foldMu alg = liftCPS $ \ (Mu f) -> appFun f (Down (Fun alg))

unfoldMu :: Traversable f => CPS r a (f a) -> CPS r a (Mu r f)
unfoldMu coalg = cps $ \ a -> Mu $ liftFun' $ \ (Down (Fun alg)) -> appCPS (refoldCPS alg coalg) a

refoldMu :: (Traversable f, Neg b) => CPS r (f b) b -> CPS r a (f a) -> CPS r a b
refoldMu f g = foldMu f Cat.<<< unfoldMu g


refold :: Functor f => (f b -> b) -> (a -> f a) -> (a -> b)
refold f g = go where go = f . fmap go . g

dnESeq :: r ••Seq r a b -> Seq r a b
dnESeq = Seq . dnE . contramap (contramap getSeq)

dnEFun :: r ••(a ~~r~> b) -> (a ~~r~> b)
dnEFun = Fun . dnE . contramap (contramap getFun)


class (Core s, Structural s, Implicative s, Universal s) => Recursive s where
  muL
    :: (ForAllC Neg Pos f, Neg a)
    => i -|s r|- o > f a ~~r~> a   ->   a < i -|s r|- o
    -- ------------------------------------------------
    ->              Mu r f < i -|s r|- o
  muL'
    :: ForAllC Neg Pos f
    =>             Mu  r f  < i -|s r|- o
    -- ----------------------------------
    -> ForAll r N (MuF r f) < i -|s r|- o
  muL' p = muR init >>> wkL' p
  muR
    :: ForAllC Neg Pos f
    => i -|s r|- o > ForAll r N (MuF r f)
    -- ----------------------------------
    -> i -|s r|- o >             Mu  r f

instance Recursive Seq where
  muL f k = wkL (downR f) >>> exL (mapL getMu (funL init (wkL' k)))
  muR = mapR mu


-- Polarity shifts

type Shifting s = (ShiftingN s, ShiftingP s)


newtype Up   a = Up   { getUp   :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Pos a => Polarized N (Up a) where


class (Core s, Structural s) => ShiftingN s where
  {-# MINIMAL (upL | upLDown), upR #-}
  upL
    :: Pos a
    =>    a < i -|s r|- o
    -- ------------------
    -> Up a < i -|s r|- o
  default upL
    :: (ShiftingP s, NegNegation s, Pos a)
    =>    a < i -|s r|- o
    -- ------------------
    -> Up a < i -|s r|- o
  upL = upLDown . downR . notR
  upLDown
    :: Pos a
    =>        i -|s r|- o > Down (r ¬a)
    -- --------------------------------
    -> Up a < i -|s r|- o
  default upLDown
    :: (ShiftingP s, NegNegation s, Pos a)
    =>        i -|s r|- o > Down (r ¬a)
    -- --------------------------------
    -> Up a < i -|s r|- o
  upLDown s = wkL s >>> downL (notL (upL init))
  upL'
    :: Pos a
    => Up a < i -|s r|- o
    -- ------------------
    ->    a < i -|s r|- o
  upL' p = upR init >>> wkL' p
  upR
    :: Pos a
    => i -|s r|- o >    a
    -- ------------------
    -> i -|s r|- o > Up a
  upR'
    :: Pos a
    => i -|s r|- o > Up a
    -- ------------------
    -> i -|s r|- o >    a
  upR' p = wkR' p >>> upL init

instance ShiftingN Seq where
  upL   = mapL getUp
  upR   = mapR Up


newtype Down a = Down { getDown :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Neg a => Polarized P (Down a) where


class (Core s, Structural s) => ShiftingP s where
  {-# MINIMAL (downL | downLUp), downR #-}
  downL
    :: Neg a
    =>      a < i -|s r|- o
    -- --------------------
    -> Down a < i -|s r|- o
  default downL
    :: (ShiftingN s, PosNegation s, Neg a)
    =>      a < i -|s r|- o
    -- --------------------
    -> Down a < i -|s r|- o
  downL = downLUp . upR . negateR
  downLUp
    :: Neg a
    =>          i -|s r|- o > Up (r -a)
    -- --------------------------------
    -> Down a < i -|s r|- o
  default downLUp
    :: (ShiftingN s, PosNegation s, Neg a)
    =>          i -|s r|- o > Up (r -a)
    -- --------------------------------
    -> Down a < i -|s r|- o
  downLUp s = wkL s >>> upL (negateL (downL init))
  downL'
    :: Neg a
    => Down a < i -|s r|- o
    -- --------------------
    ->      a < i -|s r|- o
  downL' p = downR init >>> wkL' p
  downR
    :: Neg a
    => i -|s r|- o >      a
    -- --------------------
    -> i -|s r|- o > Down a
  downR'
    :: Neg a
    => i -|s r|- o > Down a
    -- --------------------
    -> i -|s r|- o >      a
  downR' p = wkR' p >>> downL init

instance ShiftingP Seq where
  downL = mapL getDown
  downR = mapR Down


-- Utilities

type ForAllC cx cf f = (forall x . cx x => cf (f x)) :: Constraint


newtype (f · g) a = C { getC :: f (g a) }
  deriving (Eq, Foldable, Functor, Ord, Show)

infixr 7 ·

deriving instance (Traversable f, Traversable g) => Traversable (f · g)

instance Polarized p (f (g a)) => Polarized p ((f · g) a) where

instance (Applicative f, Applicative g) => Applicative (f · g) where
  pure = C . pure . pure
  f <*> a = C ((<*>) <$> getC f <*> getC a)

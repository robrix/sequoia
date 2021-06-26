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
, type (<|)
, (<|)
, type (|>)
, (|>)
, Γ(..)
, Δ
, type (-|)
, type (|-)
  -- * Core rules
, Core(..)
, Structural(..)
  -- * Control
, Control(..)
  -- * Negating
, Negating
, type (¬)(..)
, type (¬-)
, NegatingN(..)
, type (-)(..)
, type (-¬)
, NegatingP(..)
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
, type (--<)
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
import           Control.Monad (ap, join)
import           Control.Monad.Trans.Class
import           Data.Functor.Contravariant (contramap)
import           Data.Functor.Identity
import           Data.Kind (Constraint, Type)
import           Data.Profunctor
import           Focalized.CPS
import           Focalized.Connective
import           Prelude hiding (init)

-- Sequents

runSeq :: Seq r i o -> ((o -> r) -> (i -> r))
runSeq = runCPS . getSeq

evalSeq :: Seq o i o -> (i -> o)
evalSeq = (`runSeq` id)

sequent :: ((o -> r) -> (i -> r)) -> Seq r i o
sequent = Seq . CPS

newtype Seq r i o = Seq { getSeq :: CPS r i o }
  deriving (Applicative, Functor, Monad)

liftLR :: CPS r a b -> Seq r (a <| i) (o |> b)
liftLR = Seq . dimap exl inr


lowerLR :: (CPS r a b -> Seq r i o) -> Seq r (a <| i) (o |> b) -> Seq r i o
lowerLR f p = sequent $ \ k i -> runSeq (f (CPS (\ kb a -> runSeq p (k |> kb) (a <| i)))) k i


-- Effectful sequents

runSeqT :: SeqT r i m o -> ((o -> m r) -> (i -> m r))
runSeqT = runSeq . getSeqT

newtype SeqT r i m o = SeqT { getSeqT :: Seq (m r) i o }
  deriving (Applicative, Functor, Monad)

instance MonadTrans (SeqT r i) where
  lift m = SeqT (Seq (CPS (\ k _ -> m >>= k)))


-- Contexts

data a <| b = a :<| b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 4 <|, :<|

instance Conj (<|) where
  inlr = (:<|)
  exl (a :<| _) = a
  exr (_ :<| b) = b

(<|) :: i -> is -> i <| is
(<|) = inlr

data a |> b
  = L a
  | R b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 4 |>

instance Disj (|>) where
  inl = L
  inr = R
  exlr f g = \case
    L a -> f a
    R b -> g b

instance Applicative ((|>) a) where
  pure = R
  (<*>) = ap

instance Monad ((|>) a) where
  (>>=) = flip (exlr inl)

-- | Discrimination of values in '|>'.
--
-- @¬A ✕ ¬B -> ¬(A + B)@
(|>) :: (os -> r) -> (o -> r) -> ((os |> o) -> r)
(|>) = exlr


data Γ = Γ
  deriving (Eq, Ord, Show)


data Δ


type l -| r = r l
type l |- r = l r

infixl 2 |-, -|


-- Core rules

class Core s where
  {-# MINIMAL ((>>>) | (<<<)), init #-}

  (>>>)
    :: i -|s r|- o |> a   ->   a <| i -|s r|- o
    -- ----------------------------------------
    -> i -|s r|- o
  (>>>) = flip (<<<)

  (<<<)
    :: a <| i -|s r|- o   ->   i -|s r|- o |> a
    -- ----------------------------------------
    -> i -|s r|- o
  (<<<) = flip (>>>)

  infixr 1 >>>, <<<

  init
    -- ---------------------
    :: a <| i -|s r|- o |> a


instance Core Seq where
  f >>> g = f >>= pure |> pushL g

  init = popL liftR


class Core s => Structural s where
  -- | Pop something off the input context which can later be pushed. Used with 'pushL', this provides a generalized context restructuring facility.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  popL :: (a -> s r i o) -> s r (a <| i) o

  poppedL :: (s r i o -> s r i' o') -> (s r (a <| i) o -> s r (a <| i') o')
  poppedL f p = popL (f . pushL p)

  -- | Push something onto the input context which was previously popped off it. Used with 'popL', this provides a generalized context restructuring facility. It i undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  pushL :: s r (a <| i) o -> (a -> s r i o)

  popL2 :: (a -> b -> s r i o) -> s r (a <| b <| i) o
  popL2 f = popL (popL . f)

  pushL2 :: s r (a <| b <| i) o -> a -> b -> s r i o
  pushL2 p = pushL . pushL p

  mapL :: (a' -> a) -> s r (a <| i) o -> s r (a' <| i) o
  mapL f p = popL (pushL p . f)

  -- FIXME: this is clearly possible, tho it’s less clear that it’s a good idea.
  -- mapL2 :: (c -> (b, a)) -> s r (a <| i) o -> s r (b <| i) o -> s r (c <| i) o
  -- mapL2 f a b = popL (pushL b . exl . f) <|> popL (pushL a . exr . f)

  liftL :: r •a -> s r (a <| i) o
  liftL = pushR init

  lowerL :: (r •a -> s r i o) -> (s r (a <| i) o -> s r i o)
  lowerL k p = popR k >>> p


  -- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  popR :: (r •a -> s r i o) -> s r i (o |> a)

  poppedR :: (s r i o -> s r i' o') -> (s r i (o |> a) -> s r i' (o' |> a))
  poppedR f p = popR (f . pushR p)

  -- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It i undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  pushR :: s r i (o |> a) -> (r •a -> s r i o)

  popR2 :: (r •a -> r •b -> s r i o) -> s r i (o |> b |> a)
  popR2 f = popR (popR . f)

  pushR2 :: s r i (o |> b |> a) -> r •a -> r •b -> s r i o
  pushR2 p = pushR . pushR p

  mapR :: (a -> a') -> s r i (o |> a) -> s r i (o |> a')
  mapR f p = popR (pushR p . contramap f)

  mapR2 :: (a -> b -> c) -> s r i (o |> a) -> s r i (o |> b) -> s r i (o |> c)
  mapR2 f a b = popR (pushR (wkR' a) . contramap f) >>> popL (\ f -> popR (pushR b . contramap f))

  liftR :: a -> s r i (o |> a)
  liftR = pushL init

  lowerR :: (a -> s r i o) -> (s r i (o |> a) -> s r i o)
  lowerR k p = p >>> popL k


  wkL
    :: s r i o
    -- --------------
    -> s r (a <| i) o
  wkL = popL . const
  wkL'
    :: s r (a <| i) o
    -- -------------------
    -> s r (a <| b <| i) o
  wkL' = exL . wkL
  wkR
    :: s r i o
    -- --------------
    -> s r i (o |> a)
  wkR = popR . const
  wkR'
    :: s r i (o |> a)
    -- -------------------
    -> s r i (o |> b |> a)
  wkR' = exR . wkR
  cnL
    :: s r (a <| a <| i) o
    -- -------------------
    -> s r (a <| i) o
  cnL = popL . join . pushL2
  cnR
    :: s r i (o |> a |> a)
    -- -------------------
    -> s r i (o |> a)
  cnR = popR . join . pushR2
  exL
    :: s r (a <| b <| c) o
    -- -------------------
    -> s r (b <| a <| c) o
  exL = popL2 . flip . pushL2
  exR
    :: s r i (o |> a |> b)
    -- -------------------
    -> s r i (o |> b |> a)
  exR = popR2 . flip . pushR2

instance Structural Seq where
  popL f = sequent $ \ k -> uncurryConj ((`runSeq` k) . f)
  pushL s a = sequent $ \ k -> runSeq s k . (a <|)

  popR f = sequent $ \ k -> runSeq (f (K (k . inr))) (k . inl)
  pushR s a = sequent $ \ k -> runSeq s (k |> runK a)


-- Control

class (Core s, Structural s) => Control s where
  reset
    :: i -|s o|- o
    -- -----------
    -> i -|s r|- o
  shift
    :: r •a <| i -|s r|- o |> r
    -- -------------------------
    ->          i -|s r|- o |> a

  kL
    ::          i -|s r|- o |> a
    -- -------------------------
    -> r •a <| i -|s r|- o
  kL = popL . pushR

  kL'
    :: r •a <| i -|s r|- o
    -- -------------------------
    ->          i -|s r|- o |> a
  kL' s = kR init >>> wkR s

  kR
    :: a <| i -|s r|- o
    -- -------------------------
    ->      i -|s r|- o |> r •a
  kR s = lowerL (pushL init) (wkR s)

  kR'
    ::      i -|s r|- o |> r •a
    -- -------------------------
    -> a <| i -|s r|- o
  kR' s = wkL s >>> kL init


instance Control Seq where
  reset s = sequent (. evalSeq s)
  shift p = sequent (\ k -> runSeq p (k . inl |> id) . (K (k . inr) <|))


-- Negating

type Negating s = (NegatingN s, NegatingP s)


newtype r ¬a = Not    { getNot    :: r •a }

instance Pos a => Polarized N (r ¬a) where

notNegate :: r ••a -> r ¬-a
notNegate = Not . contramap getNegate

getNotNegate :: r ¬-a -> r ••a
getNotNegate = contramap Negate . getNot


type r ¬- a = r ¬r -a

infixr 9 ¬, ¬-


class (Core s, Structural s, Control s) => NegatingN s where
  notL
    :: Pos a
    =>         i -|s r|- o |> a
    -- ------------------------
    -> r ¬a <| i -|s r|- o
  notL = notLK . kL
  notLK
    :: Pos a
    => r •a <| i -|s r|- o
    -- --------------------
    ->  r ¬a <| i -|s r|- o
  notLK = mapL getNot
  notL'
    :: Pos a
    => r ¬a <| i -|s r|- o
    -- -------------------------
    ->          i -|s r|- o |> a
  notL' p = notR init >>> wkR p
  notLK'
    :: Pos a
    =>  r ¬a <| i -|s r|- o
    -- --------------------
    -> r •a <| i -|s r|- o
  notLK' = mapL Not
  notR
    :: Pos a
    => a <| i -|s r|- o
    -- ------------------------
    ->      i -|s r|- o |> r ¬a
  notR = notRK . kR
  notRK
    :: Pos a
    => i -|s r|- o |> r •a
    -- --------------------
    -> i -|s r|- o |> r ¬a
  notRK = mapR Not
  notR'
    :: Pos a
    =>      i -|s r|- o |> r ¬a
    -- ------------------------
    -> a <| i -|s r|- o
  notR' p = wkL p >>> notL init
  notRK'
    :: Pos a
    => i -|s r|- o |> r ¬a
    -- --------------------
    -> i -|s r|- o |> r •a
  notRK' = mapR getNot
  shiftP
    :: Pos a
    => r ¬a <| i -|s r|- o |> r
    -- ------------------------
    ->         i -|s r|- o |> a
  shiftP = shift . notLK'

  dneNL
    :: Neg a
    =>             a <| i -|s r|- o
    -- ----------------------------
    -> r ¬-a <| i -|s r|- o
  default dneNL
    :: (NegatingP s, Neg a)
    =>             a <| i -|s r|- o
    -- ----------------------------
    -> r ¬-a <| i -|s r|- o
  dneNL = notL . negateR
  dneNLK
    :: Neg a
    =>         r ••a <| i -|s r|- o
    -- ----------------------------
    -> r ¬-a <| i -|s r|- o
  default dneNLK
    ::         r ••a <| i -|s r|- o
    -- ----------------------------
    -> r ¬-a <| i -|s r|- o
  dneNLK = mapL getNotNegate
  dneNR
    :: Neg a
    => i -|s r|- o |> a
    -- --------------------
    -> i -|s r|- o |> r ¬-a
  default dneNR
    :: (NegatingP s, Neg a)
    => i -|s r|- o |> a
    -- --------------------
    -> i -|s r|- o |> r ¬-a
  dneNR = notR . negateL
  dneNRK
    :: Neg a
    => i -|s r|- o |> r ••a
    -- ---------------------
    -> i -|s r|- o |> r ¬-a
  default dneNRK
    :: i -|s r|- o |> r ••a
    -- ---------------------
    -> i -|s r|- o |> r ¬-a
  dneNRK = mapR notNegate

instance NegatingN Seq where


newtype r -a = Negate { getNegate :: r •a }

instance Neg a => Polarized P (r -a) where

negateNot :: r ••a -> r -¬a
negateNot = Negate . contramap getNot

getNegateNot :: r -¬a -> r ••a
getNegateNot = contramap Not . getNegate


type r -¬ a = r -r ¬a

infixr 9 -, -¬


class (Core s, Structural s, Control s) => NegatingP s where
  negateL
    :: Neg a
    =>         i -|s r|- o |> a
    -- ------------------------
    -> r -a <| i -|s r|- o
  negateL = negateLK . kL
  negateLK
    :: Neg a
    => r •a <| i -|s r|- o
    -- -------------------
    -> r -a <| i -|s r|- o
  negateLK = mapL getNegate
  negateLK'
    :: Neg a
    => r -a <| i -|s r|- o
    -- -------------------------
    ->      r •a <| i -|s r|- o
  negateLK' = mapL Negate
  negateL'
    :: Neg a
    => r -a <| i -|s r|- o
    -- ------------------------------
    ->               i -|s r|- o |> a
  negateL' p = negateR init >>> wkR p
  negateR
    :: Neg a
    => a <| i -|s r|- o
    -- ------------------------------
    ->      i -|s r|- o |> r -a
  negateR = negateRK . kR
  negateRK
    :: Neg a
    => i -|s r|- o |> r •a
    -- -------------------------
    -> i -|s r|- o |> r -a
  negateRK = mapR Negate
  negateR'
    :: Neg a
    => i -|s r|- o |> r -a
    -- -------------------------
    -> a <| i -|s r|- o
  negateR' p = wkL p >>> negateL init
  negateRK'
    :: Neg a
    => i -|s r|- o |> r -a
    -- -------------------------
    -> i -|s r|- o |> r •a
  negateRK' = mapR getNegate
  shiftN
    :: Neg a
    => r -a <| i -|s r|- o |> r
    -- ------------------------------
    ->               i -|s r|- o |> a
  shiftN = shift . negateLK'

  dnePL
    :: Pos a
    =>               a <| i -|s r|- o
    -- ------------------------------
    -> r -¬a <| i -|s r|- o
  default dnePL
    :: (NegatingN s, Pos a)
    =>               a <| i -|s r|- o
    -- ------------------------------
    -> r -¬a <| i -|s r|- o
  dnePL = negateL . notR
  dnePLK
    :: Pos a
    =>           r ••a <| i -|s r|- o
    -- ------------------------------
    -> r -¬a <| i -|s r|- o
  default dnePLK
    ::           r ••a <| i -|s r|- o
    -- ------------------------------
    -> r -¬a <| i -|s r|- o
  dnePLK = mapL getNegateNot
  dnePR
    :: Pos a
    => i -|s r|- o |> a
    -- --------------------
    -> i -|s r|- o |> r -¬a
  default dnePR
    :: (NegatingN s, Pos a)
    => i -|s r|- o |> a
    -- --------------------
    -> i -|s r|- o |> r -¬a
  dnePR = negateR . notL
  dnePRK
    :: Pos a
    => i -|s r|- o |> r ••a
    -- --------------------
    -> i -|s r|- o |> r -¬a
  default dnePRK
    :: i -|s r|- o |> r ••a
    -- --------------------
    -> i -|s r|- o |> r -¬a
  dnePRK = mapR negateNot

instance NegatingP Seq where


-- Additive

type Additive s = (AdditiveTruth s, AdditiveFalsity s, AdditiveConj s, AdditiveDisj s)


data Top = Top
  deriving (Eq, Ord, Show)

instance Polarized N Top where


class (Core s, Structural s, Negating s) => AdditiveTruth s where
  topR :: s r i (o |> Top)
  topR = liftR Top

instance AdditiveTruth Seq where


data Zero

instance Polarized P Zero where

absurdP :: Zero -> a
absurdP = \case


class (Core s, Structural s, Negating s) => AdditiveFalsity s where
  zeroL :: s r (Zero <| i) o
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


class (Core s, Structural s, Negating s) => AdditiveConj s where
  {-# MINIMAL (withL1, withL2 | withLSum), withR #-}
  withL1 :: (Neg a, Neg b) => s r (a <| i) o -> s r (a & b <| i) o
  default withL1 :: (Neg a, Neg b, AdditiveDisj s) => s r (a <| i) o -> s r (a & b <| i) o
  withL1 = withLSum . sumR1 . negateR
  withL2 :: (Neg a, Neg b) => s r (b <| i) o -> s r (a & b <| i) o
  default withL2 :: (Neg a, Neg b, AdditiveDisj s) => s r (b <| i) o -> s r (a & b <| i) o
  withL2 = withLSum . sumR2 . negateR
  withLSum :: (Neg a, Neg b) => s r i (o |> r -a ⊕ r -b) -> s r (a & b <| i) o
  default withLSum :: (Neg a, Neg b, AdditiveDisj s) => s r i (o |> r -a ⊕ r -b) -> s r (a & b <| i) o
  withLSum p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))
  withR :: (Neg a, Neg b) => s r i (o |> a) -> s r i (o |> b) -> s r i (o |> (a & b))
  withR1' :: (Neg a, Neg b) => s r i (o |> (a & b)) -> s r i (o |> a)
  withR1' t = wkR' t >>> withL1 init
  withR2' :: (Neg a, Neg b) => s r i (o |> (a & b)) -> s r i (o |> b)
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


class (Core s, Structural s, Negating s) => AdditiveDisj s where
  {-# MINIMAL (sumL | sumLWith), sumR1, sumR2 #-}
  sumL :: (Pos a, Pos b) => s r (a <| i) o -> s r (b <| i) o -> s r (a ⊕ b <| i) o
  default sumL :: (Pos a, Pos b, AdditiveConj s) => s r (a <| i) o -> s r (b <| i) o -> s r (a ⊕ b <| i) o
  sumL p1 p2 = sumLWith (withR (notR p1) (notR p2))
  sumL1' :: (Pos a, Pos b) => s r (a ⊕ b <| i) o -> s r (a <| i) o
  sumL1' p = sumR1 init >>> wkL' p
  sumL2' :: (Pos a, Pos b) => s r (a ⊕ b <| i) o -> s r (b <| i) o
  sumL2' p = sumR2 init >>> wkL' p
  sumLWith :: (Pos a, Pos b) => s r i (o |> r ¬a & r ¬b) -> s r (a ⊕ b <| i) o
  default sumLWith :: (Pos a, Pos b, AdditiveConj s) => s r i (o |> r ¬a & r ¬b) -> s r (a ⊕ b <| i) o
  sumLWith p = sumL (wkL p >>> withL1 (notL init)) (wkL p >>> withL2 (notL init))
  sumR1 :: (Pos a, Pos b) => s r i (o |> a) -> s r i (o |> a ⊕ b)
  sumR2 :: (Pos a, Pos b) => s r i (o |> b) -> s r i (o |> a ⊕ b)

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


class (Core s, Structural s, Negating s) => MultiplicativeFalsity s where
  botL :: s r (Bot <| i) o
  botL = liftL (K absurdN)
  botR :: s r i o -> s r i (o |> Bot)
  botR = wkR
  botR' :: s r i (o |> Bot) -> s r i o
  botR' = (>>> botL)

instance MultiplicativeFalsity Seq where


data One = One
  deriving (Eq, Ord, Show)

instance Polarized P One where


class (Core s, Structural s, Negating s) => MultiplicativeTruth s where
  oneL :: s r i o -> s r (One <| i) o
  oneL = wkL
  oneL' :: s r (One <| i) o -> s r i o
  oneL' = (oneR >>>)
  oneR :: s r i (o |> One)
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


class (Core s, Structural s, Negating s) => MultiplicativeDisj s where
  {-# MINIMAL (parL | parLTensor), parR #-}
  parL :: (Neg a, Neg b) => s r (a <| i) o -> s r (b <| i) o -> s r (a ⅋ b <| i) o
  default parL :: (Neg a, Neg b, MultiplicativeConj s) => s r (a <| i) o -> s r (b <| i) o -> s r (a ⅋ b <| i) o
  parL p1 p2 = parLTensor (tensorR (negateR p1) (negateR p2))
  parLTensor :: (Neg a, Neg b) => s r i (o |> r -a ⊗ r -b) -> s r (a ⅋ b <| i) o
  default parLTensor :: (Neg a, Neg b, MultiplicativeConj s) => s r i (o |> r -a ⊗ r -b) -> s r (a ⅋ b <| i) o
  parLTensor p = wkL p >>> tensorL (negateL (negateL (parL (wkR init) init)))
  parR :: (Neg a, Neg b) => s r i (o |> a |> b) -> s r i (o |> a ⅋ b)
  parR' :: (Neg a, Neg b) => s r i (o |> a ⅋ b) -> s r i (o |> a |> b)
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


class (Core s, Structural s, Negating s) => MultiplicativeConj s where
  {-# MINIMAL (tensorL | tensorLPar), tensorR #-}
  tensorL :: (Pos a, Pos b) => s r (a <| b <| i) o -> s r (a ⊗ b <| i) o
  default tensorL :: (Pos a, Pos b, MultiplicativeDisj s) => s r (a <| b <| i) o -> s r (a ⊗ b <| i) o
  tensorL = tensorLPar . parR . notR . notR
  tensorLPar :: (Pos a, Pos b) => s r i (o |> r ¬a ⅋ r ¬b) -> s r (a ⊗ b <| i) o
  default tensorLPar :: (Pos a, Pos b, MultiplicativeDisj s) => s r i (o |> r ¬a ⅋ r ¬b) -> s r (a ⊗ b <| i) o
  tensorLPar p = wkL p >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
  tensorL' :: (Pos a, Pos b) => s r (a ⊗ b <| i) o -> s r (a <| b <| i) o
  tensorL' p = tensorR init (wkL init) >>> popL (wkL . wkL . pushL p)
  tensorR :: (Pos a, Pos b) => s r i (o |> a) -> s r i (o |> b) -> s r i (o |> a ⊗ b)

instance MultiplicativeConj Seq where
  tensorL p = popL (pushL2 p . exl <*> exr)
  tensorR = liftA2 (liftA2 inlr)


-- Implicative

runFun :: (a ~~r~> b) -> Seq r (a <| i) (o |> b)
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

class (Core s, Structural s, Negating s) => Implicative s where
  {-# MINIMAL (funL | funLSub), funR #-}
  funL :: (Pos a, Neg b) => s r i (o |> a) -> s r (b <| i) o -> s r (a ~~r~> b <| i) o
  default funL :: (Pos a, Neg b, Coimplicative s) => s r i (o |> a) -> s r (b <| i) o -> s r (a ~~r~> b <| i) o
  funL pa pb = funLSub (subR pa pb)
  funLSub :: (Pos a, Neg b) => s r i (o |> (a --< b) r) -> s r (a ~~r~> b <| i) o
  default funLSub :: (Pos a, Neg b, Coimplicative s) => s r i (o |> (a --< b) r) -> s r (a ~~r~> b <| i) o
  funLSub p = wkL p >>> subL (exL (funL init init))
  funL2 :: (Pos a, Neg b) => s r (a ~~r~> b <| a <| i)  (o |> b)
  funL2 = funL init init
  funR :: (Pos a, Neg b) => s r (a <| i) (o |> b) -> s r i (o |> a ~~r~> b)
  ($$) :: (Pos a, Neg b) => s r i (o |> a ~~r~> b) -> s r i (o |> a) -> s r i (o |> b)
  f $$ a = wkR' f >>> wkR' a `funL` init
  funR' :: (Pos a, Neg b) => s r i (o |> a ~~r~> b) -> s r (a <| i) (o |> b)
  funR' p = wkL (wkR' p) >>> funL2

instance Implicative Seq where
  funL a b = popL (\ f -> a >>> runFun f >>> wkL' b)
  funR = lowerLR (liftR . Fun) . wkR'


data Sub r a b = Sub { subA :: !a, subK :: !(r -b) }

instance (Pos a, Neg b) => Polarized P (Sub r a b) where

type (a --< b) r = Sub r a b

infixr 5 --<


class (Core s, Structural s, Negating s) => Coimplicative s where
  {-# MINIMAL (subL | subLFun), subR #-}
  subL :: (Pos a, Neg b) => s r (a <| i) (o |> b) -> s r ((a --< b) r <| i) o
  default subL :: (Pos a, Neg b, Implicative s) => s r (a <| i) (o |> b) -> s r ((a --< b) r <| i) o
  subL = subLFun . funR
  subLFun :: (Pos a, Neg b) => s r i (o |> a ~~r~> b) -> s r ((a --< b) r <| i) o
  default subLFun :: (Pos a, Neg b, Implicative s) => s r i (o |> a ~~r~> b) -> s r ((a --< b) r <| i) o
  subLFun p = wkL p >>> exL (subL (exL (funL init init)))
  subL' :: (Pos a, Neg b) => s r ((a --< b) r <| i) o -> s r (a <| i) (o |> b)
  subL' p = subR init init >>> wkR (wkL' p)
  subR :: (Pos a, Neg b) => s r i (o |> a) -> s r (b <| i) o -> s r i (o |> (a --< b) r)

instance Coimplicative Seq where
  subL b = popL (\ s -> liftR (subA s) >>> b >>> liftL (getNegate (subK s)))
  subR a b = liftA2 Sub <$> a <*> negateR b


-- Quantifying

type Quantifying s = (Universal s, Existential s)


newtype ForAll r p f = ForAll { runForAll :: forall x . Polarized p x => r ••f x }

instance Polarized N (ForAll r p f)


class (Core s, Structural s, Negating s, Shifting s) => Universal s where
  {-# MINIMAL (forAllL | forAllLExists), forAllR #-}
  forAllL :: (Polarized n x, Neg (f x)) => s r (r ¬-f x <| i) o -> s r (ForAll r n f <| i) o
  default forAllL :: (Polarized n x, ForAllC (Polarized n) Neg f, Existential s) => s r (r ¬-f x <| i) o -> s r (ForAll r n f <| i) o
  forAllL p = forAllLExists (existsR (mapR C (notL' p)))
  forAllLExists :: ForAllC (Polarized n) Neg f => s r i (o |> Exists r n ((-) r · f)) -> s r (ForAll r n f <| i) o
  default forAllLExists :: (ForAllC (Polarized n) Neg f, Existential s) => s r i (o |> Exists r n ((-) r · f)) -> s r (ForAll r n f <| i) o
  forAllLExists p = wkL p >>> existsL (mapL getC (negateL (forAllL (notL (negateR init)))))
  -- FIXME: the correct signature should be s r i (o |> (forall x . Polarized n x => f x)) -> s r i (o |> ForAll f), but we can’t write that until (at least) quick look impredicativity lands in ghc (likely 9.2)
  forAllR :: ForAllC (Polarized n) Neg f => (forall x . Polarized n x => s r i (o |> f x)) -> s r i (o |> ForAll r n f)
  forAllR' :: ForAllC (Polarized n) Neg f => s r i (o |> ForAll r n f) -> (forall x . Polarized n x => s r i (o |> f x))
  forAllR' p = wkR' p >>> forAllL (dneNL init)

instance Universal Seq where
  forAllL p = mapL (notNegate . runForAll) p
  forAllR p = sequent $ \ k a -> k (inr (ForAll (K (\ k' -> runSeq p (k . inl |> runK k') a))))


data Exists r p f = forall x . Polarized p x => Exists (r ••f x)

instance Polarized P (Exists r p f)

runExists :: (forall x . Polarized p x => f x -> a) -> Exists r p f -> r ••a
runExists f (Exists r) = K (\ k -> runK r (K (runK k . f)))


class (Core s, Structural s, Negating s, Shifting s) => Existential s where
  {-# MINIMAL (existsL | existsLForAll), existsR #-}
  -- FIXME: the correct signature should be s r ((forall x . f x) <| i) o -> s r (Exists f <| i) o, but we can’t write that until (at least) quick look impredicativity lands in ghc (likely 9.2)
  existsL :: (forall x . Polarized n x => s r (f x <| i) o) -> s r (Exists r n f <| i) o
  default existsL :: (ForAllC (Polarized n) Pos f, Universal s) => (forall x . Polarized n x => s r (f x <| i) o) -> s r (Exists r n f <| i) o
  existsL s = existsLForAll (forAllR (mapR C (notR s)))
  existsL' :: ForAllC (Polarized n) Pos f => s r (Exists r n f <| i) o -> (forall x . Polarized n x => s r (f x <| i) o)
  existsL' p = existsR init >>> wkL' p
  existsLForAll :: ForAllC (Polarized n) Pos f => s r i (o |> ForAll r n ((¬) r · f)) -> s r (Exists r n f <| i) o
  default existsLForAll :: (ForAllC (Polarized n) Pos f, Universal s) => s r i (o |> ForAll r n ((¬) r · f)) -> s r (Exists r n f <| i) o
  existsLForAll p = wkL p >>> exL (existsL (exL (forAllL (notL (negateR (mapL getC (notL init)))))))
  existsR :: (Polarized n x, Pos (f x)) => s r i (o |> f x) -> s r i (o |> Exists r n f)

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
  nuL :: ForAllC Pos Neg f => s r (Exists r P (NuF r f) <| i) o -> s r (Nu r f <| i) o
  nuR :: ForAllC Pos Neg f => s r i (o |> Exists r P (NuF r f)) -> s r i (o |> Nu r f)
  nuR' :: ForAllC Pos Neg f => s r i (o |> Nu r f) -> s r i (o |> Exists r P (NuF r f))
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
    => s r i (o |> f a ~~r~> a)   ->   s r (a <| i) o
    -------------------------------------------------
    -> s r (Mu r f <| i) o
  muL' :: ForAllC Neg Pos f => s r (Mu r f <| i) o -> s r (ForAll r N (MuF r f) <| i) o
  muL' p = muR init >>> wkL' p
  muR :: ForAllC Neg Pos f => s r i (o |> ForAll r N (MuF r f)) -> s r i (o |> Mu r f)

instance Recursive Seq where
  muL f k = wkL (downR f) >>> exL (mapL getMu (funL init (wkL' k)))
  muR = mapR mu


-- Polarity

newtype N a = N { getN :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity


newtype P a = P { getP :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity


class Polarized (p :: Type -> Type) c | c -> p
instance Polarized N (N a)
instance Polarized P (P a)
instance (Pos a, Neg b) => Polarized N (a -> b)

type Neg = Polarized N
type Pos = Polarized P


type Shifting s = (ShiftingN s, ShiftingP s)


newtype Up   a = Up   { getUp   :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity

instance Pos a => Polarized N (Up a) where


class (Core s, Structural s) => ShiftingN s where
  {-# MINIMAL (upL | upLDown), upR #-}
  upL :: Pos a => s r (a <| i) o -> s r (Up a <| i) o
  default upL :: (ShiftingP s, NegatingN s, Pos a) => s r (a <| i) o -> s r (Up a <| i) o
  upL = upLDown . downR . notR
  upLDown :: Pos a => s r i (o |> Down (r ¬a)) -> s r (Up a <| i) o
  default upLDown :: (ShiftingP s, NegatingN s, Pos a) => s r i (o |> Down (r ¬a)) -> s r (Up a <| i) o
  upLDown s = wkL s >>> downL (notL (upL init))
  upL' :: Pos a => s r (Up a <| i) o -> s r (a <| i) o
  upL' p = upR init >>> wkL' p
  upR :: Pos a => s r i (o |> a) -> s r i (o |> Up a)
  upR' :: Pos a => s r i (o |> Up a) -> s r i (o |> a)
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
  downL :: Neg a => s r (a <| i) o -> s r (Down a <| i) o
  default downL :: (ShiftingN s, NegatingP s, Neg a) => s r (a <| i) o -> s r (Down a <| i) o
  downL = downLUp . upR . negateR
  downLUp :: Neg a => s r i (o |> Up (r -a)) -> s r (Down a <| i) o
  default downLUp :: (ShiftingN s, NegatingP s, Neg a) => s r i (o |> Up (r -a)) -> s r (Down a <| i) o
  downLUp s = wkL s >>> upL (negateL (downL init))
  downL' :: Neg a => s r (Down a <| i) o -> s r (a <| i) o
  downL' p = downR init >>> wkL' p
  downR :: Neg a => s r i (o |> a) -> s r i (o |> Down a)
  downR' :: Neg a => s r i (o |> Down a) -> s r i (o |> a)
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

{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
module Focalized.Calculus
( Core(..)
, Structural(..)
, Negative(..)
, Additive(..)
, Multiplicative(..)
, Implicative(..)
, N(..)
, P(..)
, Γ(..)
, Δ
, type (|-)(..)
, runSeq
, runSeqIO
) where

import Control.Applicative (liftA2)
import Control.Exception (Exception, catch, throw)
import Control.Monad (ap, join)
import Data.Bifoldable
import Data.Bifunctor (Bifunctor(..))
import Data.Bitraversable
import Data.Functor.Identity
import Prelude hiding (init, tail)

type (*) = (,)
infixr 4 *

type (+) = Either
infixl 4 +

split :: (os + a -> r) -> (os -> r, a -> r)
split f = (f . Left, f . Right)


data a ⊗ b = !a :⊗ !b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 ⊗

instance Bifoldable (⊗) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⊗) where
  bimap = bimapDefault

instance Bitraversable (⊗) where
  bitraverse f g (a :⊗ b) = (:⊗) <$> f a <*> g b

newtype a & b = With (forall r . (a -> b -> r) -> r)
  deriving (Functor)

infixr 6 &

instance Bifoldable (&) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (&) where
  bimap = bimapDefault

instance Bitraversable (&) where
  bitraverse f g w = fmap getN . inlr <$> traverse f (exl (N w)) <*> traverse g (exr (N w))

class Conj p c | c -> p where
  inlr :: p a -> p b -> p (a `c` b)
  exl :: p (a `c` b) -> p a
  exr :: p (a `c` b) -> p b

instance Conj P (⊗) where
  inlr (P a) (P b) = P (a :⊗ b)
  exl = fmap (\ (l :⊗ _) -> l)
  exr = fmap (\ (_ :⊗ r) -> r)

instance Conj N (&) where
  inlr (N a) (N b) = N $ With $ \ f -> f a b
  exl = fmap (\ (With run) -> run const)
  exr = fmap (\ (With run) -> run (const id))

data a ⊕ b
  = InL !a
  | InR !b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 6 ⊕

instance Bifoldable (⊕) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⊕) where
  bimap = bimapDefault

instance Bitraversable (⊕) where
  bitraverse f g = \case
    InL a -> InL <$> f a
    InR b -> InR <$> g b

newtype a ⅋ b = Par (forall r . (a -> r) -> (b -> r) -> r)
  deriving (Functor)

infixr 7 ⅋

instance Bifoldable (⅋) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (⅋) where
  bimap = bimapDefault

instance Bitraversable (⅋) where
  bitraverse f g (Par run) = run (fmap (getN . inl . N) . f) (fmap (getN . inr . N) . g)

class Disj p d | d -> p where
  inl :: p a -> p (a `d` b)
  inr :: p b -> p (a `d` b)
  exlr :: (p a -> r) -> (p b -> r) -> (p (a `d` b) -> r)

instance Disj P (⊕) where
  inl = fmap InL
  inr = fmap InR
  exlr ifl ifr = \case
    P (InL l) -> ifl (P l)
    P (InR r) -> ifr (P r)

instance Disj N (⅋) where
  inl (N l) = N $ Par $ \ ifl _ -> ifl l
  inr (N r) = N $ Par $ \ _ ifr -> ifr r
  exlr ifl ifr (N (Par run)) = run (ifl . N) (ifr . N)

newtype a --> b = Fun { appFun :: (N b -> Δ) -> (P a -> Δ) }

infixr 5 -->

fun :: ((N b -> Δ) -> (P a -> Δ)) -> N (a --> b)
fun = N . Fun

data a --< b = Sub { subA :: !(P a), subK :: !(P (Negate b)) }

infixr 5 --<

sub :: P a -> P (Negate b) -> P (a --< b)
sub = fmap P . Sub

newtype Not    a = Not    { runNot    :: P a -> Δ }

not' :: (P a -> Δ) -> N (Not a)
not' = N . Not

newtype Negate a = Negate { runNegate :: N a -> Δ }

negate' :: (N a -> Δ) -> P (Negate a)
negate' = P . Negate

data Bot
data Top = Top
  deriving (Eq, Ord, Show)

data Zero
data One = One
  deriving (Eq, Ord, Show)


newtype N a = N { getN :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity
newtype P a = P { getP :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
  deriving (Applicative, Monad) via Identity


data Γ = Γ
  deriving (Eq, Ord, Show)

data Δ

absurdΔ :: Δ -> a
absurdΔ = \case


class Core p where
  (>>>) :: is `p` (os + a) -> (a * is) `p` os -> is `p` os

  init :: (a * is) `p` (os + a)

infixr 1 >>>


class Structural p where
  -- | Pop something off the input context which can later be pushed. Used with 'pushL', this provides a generalized context restructuring facility.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  popL :: (a -> is `p` os) -> (a * is) `p` os

  -- | Push something onto the input context which was previously popped off it. Used with 'popL', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popL . pushL = id
  -- @
  -- @
  -- pushL . popL = id
  -- @
  pushL :: (a * is) `p` os -> a -> is `p` os

  popL2 :: (a -> b -> is `p` os) -> (a * b * is) `p` os
  popL2 f = popL (popL . f)

  pushL2 :: (a * b * is) `p` os -> a -> b -> is `p` os
  pushL2 p = pushL . pushL p


  -- | Pop something off the output context which can later be pushed. Used with 'pushR', this provides a generalized context restructuring facility.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  popR :: ((a -> Δ) -> is `p` os) -> is `p` (os + a)

  -- | Push something onto the output context which was previously popped off it. Used with 'popR', this provides a generalized context restructuring facility. It is undefined what will happen if you push something which was not previously popped.
  --
  -- @
  -- popR . pushR = id
  -- @
  -- @
  -- pushR . popR = id
  -- @
  pushR :: is `p` (os + a) -> ((a -> Δ) -> is `p` os)

  popR2 :: ((a -> Δ) -> (b -> Δ) -> is `p` os) -> is `p` (os + b + a)
  popR2 f = popR (popR . f)

  pushR2 :: is `p` (os + b + a) -> (a -> Δ) -> (b -> Δ) -> is `p` os
  pushR2 p = pushR . pushR p


  wkL :: is `p` os -> (a * is) `p` os
  wkL = popL . const
  wkR :: is `p` os -> is `p` (os + a)
  wkR = popR . const
  cnL :: (a * a * is) `p` os -> (a * is) `p` os
  cnL = popL . join . pushL2
  cnR :: is `p` (os + a + a) -> is `p` (os + a)
  cnR = popR . join . pushR2
  exL :: (a * b * c) `p` os -> (b * a * c) `p` os
  exL = popL2 . flip . pushL2
  exR :: is `p` (os + a + b) -> is `p` (os + b + a)
  exR = popR2 . flip . pushR2


class (Core p, Structural p) => Negative p where
  negateL :: is `p` (os + N a) -> (P (Negate a) * is) `p` os
  negateL' :: (P (Negate a) * is) `p` os -> is `p` (os + N a)
  negateL' p = negateR init >>> wkR p
  negateR :: (N a * is) `p` os -> is `p` (os + P (Negate a))
  negateR' :: is `p` (os + P (Negate a)) -> (N a * is) `p` os
  negateR' p = wkL p >>> negateL init

  notL :: is `p` (os + P a) -> (N (Not a) * is) `p` os
  notL' :: (N (Not a) * is) `p` os -> is `p` (os + P a)
  notL' p = notR init >>> wkR p
  notR :: (P a * is) `p` os -> is `p` (os + N (Not a))
  notR' :: is `p` (os + N (Not a)) -> (P a * is) `p` os
  notR' p = wkL p >>> notL init


class (Core p, Structural p, Negative p) => Additive p where
  zeroL :: (P Zero * is) `p` os

  topR :: is `p` (os + N Top)

  sumL :: (P a * is) `p` os -> (P b * is) `p` os -> (P (a ⊕ b) * is) `p` os
  sumL p1 p2 = sumLWith (notR p1 & notR p2)
  sumL1' :: (P (a ⊕ b) * is) `p` os -> (P a * is) `p` os
  sumL1' p = sumR1 init >>> exL (wkL p)
  sumL2' :: (P (a ⊕ b) * is) `p` os -> (P b * is) `p` os
  sumL2' p = sumR2 init >>> exL (wkL p)
  sumLWith :: is `p` (os + N (Not a & Not b)) -> (P (a ⊕ b) * is) `p` os
  sumLWith p = wkL p >>> exL (sumL (exL (withL1 (notL init))) (exL (withL2 (notL init))))
  sumR1 :: is `p` (os + P a) -> is `p` (os + P (a ⊕ b))
  sumR2 :: is `p` (os + P b) -> is `p` (os + P (a ⊕ b))

  withL1 :: (N a * is) `p` os -> (N (a & b) * is) `p` os
  withL1 = withLSum . sumR1 . negateR
  withL2 :: (N b * is) `p` os -> (N (a & b) * is) `p` os
  withL2 = withLSum . sumR2 . negateR
  withLSum :: is `p` (os + P (Negate a ⊕ Negate b)) -> (N (a & b) * is) `p` os
  withLSum p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))
  (&) :: is `p` (os + N a) -> is `p` (os + N b) -> is `p` (os + N (a & b))
  withR1' :: is `p` (os + N (a & b)) -> is `p` (os + N a)
  withR1' t = exR (wkR t) >>> withL1 init
  withR2' :: is `p` (os + N (a & b)) -> is `p` (os + N b)
  withR2' t = exR (wkR t) >>> withL2 init

  zapSum :: is `p` (os + N (Not a & Not b)) -> (P (a ⊕ b) * is) `p` os
  zapSum p = sumL (wkL p >>> withL1 (notL init)) (wkL p >>> withL2 (notL init))

  zapWith :: is `p` (os + P (Negate a ⊕ Negate b)) -> (N (a & b) * is) `p` os
  zapWith p = wkL p >>> sumL (negateL (withL1 init)) (negateL (withL2 init))


class (Core p, Structural p, Negative p) => Multiplicative p where
  botL :: (N Bot * is) `p` os
  botR :: is `p` os -> is `p` (os + N Bot)
  botR' :: is `p` (os + N Bot) -> is `p` os
  botR' = (>>> botL)

  oneL :: is `p` os -> (P One * is) `p` os
  oneL' :: (P One * is) `p` os -> is `p` os
  oneL' = (oneR >>>)
  oneR :: is `p` (os + P One)

  parL :: (N a * is) `p` os -> (N b * is) `p` os -> (N (a ⅋ b) * is) `p` os
  parL p1 p2 = parLTensor (negateR p1 ⊗ negateR p2)
  parLTensor :: is `p` (os + P (Negate a ⊗ Negate b)) -> (N (a ⅋ b) * is) `p` os
  parLTensor p = wkL p >>> tensorL (negateL (negateL (parL (wkR init) init)))
  parR :: is `p` (os + N a + N b) -> is `p` (os + N (a ⅋ b))
  parR' :: is `p` (os + N (a ⅋ b)) -> is `p` (os + N a + N b)
  parR' p = exR (wkR (exR (wkR p))) >>> parL (wkR init) init

  tensorL :: (P a * P b * is) `p` os -> (P (a ⊗ b) * is) `p` os
  tensorL = tensorLPar . parR . notR . notR
  tensorLPar :: is `p` (os + N (Not a ⅋ Not b)) -> (P (a ⊗ b) * is) `p` os
  tensorLPar p = wkL p >>> parL (notL (tensorL init)) (notL (tensorL (wkL init)))
  tensorL' :: (P (a ⊗ b) * is) `p` os -> (P a * P b * is) `p` os
  tensorL' p = init ⊗ wkL init >>> popL (wkL . wkL . pushL p)
  (⊗) :: is `p` (os + P a) -> is `p` (os + P b) -> is `p` (os + P (a ⊗ b))

  zapTensor :: is `p` (os + N (Not a ⅋ Not b)) -> (P (a ⊗ b) * is) `p` os
  zapTensor p = tensorL (wkL (wkL p) >>> parL (notL init) (notL (wkL init)))

  zapPar :: is `p` (os + P (Negate a ⊗ Negate b)) -> (N (a ⅋ b) * is) `p` os
  zapPar p = wkL p >>> tensorL (popL2 (parL `on0` pushL (negateL init) `on1` pushL (negateL init)))


class (Core p, Structural p, Negative p) => Implicative p where
  funL :: is `p` (os + P a) -> (N b * is) `p` os -> (N (a --> b) * is) `p` os
  funL pa pb = funLSub (subR pa pb)
  funLSub :: is `p` (os + P (a --< b)) -> (N (a --> b) * is) `p` os
  funLSub p = wkL p >>> subL (exL (funL init init))
  funL2 :: (N (a --> b) * P a * is) `p` (os + N b)
  funL2 = funL init init
  funR :: (P a * is) `p` (os + N b) -> is `p` (os + N (a --> b))
  funR' :: is `p` (os + N (a --> b)) -> (P a * is) `p` (os + N b)
  funR' p = wkL (exR (wkR p)) >>> funL2

  subL :: (P a * is) `p` (os + N b) -> (P (a --< b) * is) `p` os
  subL = subLFun . funR
  subLFun :: is `p` (os + N (a --> b)) -> (P (a --< b) * is) `p` os
  subLFun p = wkL p >>> exL (subL (exL (funL init init)))
  subL' :: (P (a --< b) * is) `p` os -> (P a * is) `p` (os + N b)
  subL' p = subR init init >>> wkR (exL (wkL p))
  subR :: is `p` (os + P a) -> (N b * is) `p` os -> is `p` (os + P (a --< b))

  ($$) :: is `p` (os + N (a --> b)) -> is `p` (os + P a) -> is `p` (os + N b)
  f $$ a = exR (wkR f) >>> exR (wkR a) `funL` init

on0 :: (a -> b -> c) -> (a' -> a) -> (a' -> b -> c)
on0 = (.)

on1 :: (a -> b -> c) -> (b' -> b) -> (a -> b' -> c)
on1 = fmap flip . (.) . flip

infixl 4 `on0`, `on1`


newtype is |- os = Seq ((os -> Δ) -> (is -> Δ))
  deriving (Functor)

infix 2 |-

runSeq :: (os -> Δ) -> is -> is |- os -> Δ
runSeq k c (Seq run) = run k c

runSeqIO :: (os -> IO ()) -> is -> is |- os -> IO ()
runSeqIO k is (Seq run) = absurdΔ (run (throw . Escape . k) is) `catch` getEscape

newtype Escape = Escape { getEscape :: IO () }

instance Show Escape where show _ = "Escape"
instance Exception Escape

instance Applicative ((|-) is) where
  pure a = Seq $ \ k _ -> k a
  (<*>) = ap

instance Monad ((|-) is) where
  Seq a >>= f = Seq $ \ k c -> a (runSeq k c . f) c


instance Core (|-) where
  f >>> g = f >>= either pure (pushL g)

  init = popL (pure . pure)

instance Structural (|-) where
  popL f = Seq $ \ k -> uncurry (flip (runSeq k) . f)
  pushL (Seq run) a = Seq $ \ k -> run k . (a,)

  popR f = Seq $ \ k c -> let (k', ka) = split k in runSeq k' c (f ka)
  pushR (Seq run) a = Seq $ \ k -> run (either k a)

instance Negative (|-) where
  negateL (Seq run) = Seq $ \ k (P negA, c) -> run (either k (runNegate negA)) c
  negateR (Seq run) = Seq $ \ k c -> let (k', ka) = split k in ka (negate' (run k' . (,c)))

  notL (Seq run) = Seq $ \ k (N notA, c) -> run (either k (runNot notA)) c
  notR (Seq run) = Seq $ \ k c -> let (k', ka) = split k in ka (not' (run k' . (,c)))

instance Additive (|-) where
  zeroL = popL absurdP

  topR = pure (pure (N Top))

  sumL a b = popL (exlr (pushL a) (pushL b))
  sumR1 = fmap (fmap inl)
  sumR2 = fmap (fmap inr)

  withL1 p = popL (pushL p . exl)
  withL2 p = popL (pushL p . exr)
  (&) = liftA2 (liftA2 inlr)

instance Multiplicative (|-) where
  botL = popL absurdN
  botR = fmap Left

  oneL = wkL
  oneR = pure (pure (P One))

  parL a b = popL (exlr (pushL a) (pushL b))
  parR ab = either (>>= (pure . inl)) (pure . inr) <$> ab

  tensorL p = popL (pushL2 p . exl <*> exr)
  (⊗) = liftA2 (liftA2 inlr)

instance Implicative (|-) where
  funL a b = popL (\ (N f) -> a >>> Seq (\ k (a, is) -> appFun f (runSeq k is . pushL b) a))
  funR (Seq run) = Seq $ \ k c -> let (k', ka) = split k in ka (fun (\ kb -> run (either k' kb) . (,c)))

  subL b = popL (\ (P s) -> pushL b (subA s) >>> pushL (negateL init) (subK s))
  subR a b = liftA2 sub <$> a <*> negateR b


absurdN :: N Bot -> a
absurdN = \case

absurdP :: P Zero -> a
absurdP = \case

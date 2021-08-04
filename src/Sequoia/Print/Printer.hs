-- | Pretty-printing.
module Sequoia.Print.Printer
( -- * Printers
  Printer(..)
  -- * Construction
, printer
, withSubject
, contrapure
  -- * Elimination
, print
  -- * Computation
, (<#>)
, (<&>)
, (<&)
, liftP2
, pair
  -- * Documents
, Doc(..)
  -- * Coexponentials
, type (>-)(..)
, (>-)
, coK
, coconst
) where

import Data.Functor.Contravariant
import Data.Monoid (Endo(..))
import Data.Profunctor
import Prelude hiding (print)
import Sequoia.Print.Class
import Sequoia.Profunctor.Continuation

-- Printers

newtype Printer a = Printer { runPrint :: forall r . Doc • r -> a • r }

instance Semigroup (Printer a) where
  p1 <> p2 = Printer (\ k -> K (\ a -> runPrint p1 (K (\ a' -> runPrint p2 (lmap (mappend a') k) • a)) • a))

instance Monoid (Printer a) where
  mempty = Printer (constK . (• mempty))

instance Print (Printer a) where
  char c = Printer (constK . (• char c))
  string s = Printer (constK . (• string s))

instance Contravariant Printer where
  contramap f (Printer r) = Printer (lmap f . r)


-- Construction

printer :: (forall r . Doc • r -> a -> r) -> Printer a
printer f = Printer (K . f)

withSubject :: (a -> Printer a) -> Printer a
withSubject f = Printer (\ k -> K (\ a -> runPrint (f a) k • a))

contrapure :: (b -> a) -> Printer (a >- b)
contrapure f = Printer (\ k -> K (\ (pa :>- b) -> runPrint pa k • f b))


-- Elimination

print :: Printer a -> a -> Doc
print p = (runPrint p idK •)


-- Computation

(<#>) :: (b >- a) -> Printer a -> Printer b
f <#> a = Printer (\ k -> K (\ b -> runPrint a (K (\ a -> runPrint (coK f) (K ((k •) . mappend a)) • b)) • coconst f))

infixl 4 <#>

(<&>) :: Printer (a >- b) -> Printer a -> Printer b
pf <&> pa = Printer (\ k -> K (\ b -> runPrint pf k • (pa >- b)))

infixl 4 <&>

(<&) :: Printer a -> Printer b -> Printer a
a <& b = contramap coconst a <&> b

infixl 4 <&

liftP2 :: ((b >- c) >- a) -> Printer a -> Printer b -> Printer c
liftP2 f a b = f <#> a <&> b

pair :: Printer a -> Printer b -> Printer (a, b)
pair a b = pairP <&> a <&> b

pairP :: Printer (a >- b >- (a, b))
pairP = Printer (\ k -> K (\ (pa :>- pb :>- (a, b)) ->
  runPrint pa (K (\ da -> runPrint pb (K (\ db -> k • parens (da <> comma <+> db))) • b)) • a))


-- Documents

newtype Doc = Doc { getDoc :: ShowS }
  deriving (Monoid, Semigroup) via Endo String

instance Print Doc where
  char c = Doc (c:)
  string s = Doc (s<>)


-- Coexponentials

data a >- b = Printer a :>- b
  deriving (Functor)

infixr 0 >-, :>-

instance Profunctor (>-) where
  dimap f g (a :>- b) = contramap f a >- g b


(>-) :: Printer a -> b -> a >- b
(>-) = (:>-)


coK :: (a >- b) -> Printer a
coK (k :>- _) = k

coconst :: (a >- b) -> b
coconst (_ :>- a) = a

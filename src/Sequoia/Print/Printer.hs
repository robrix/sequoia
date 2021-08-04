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
, appPrint
  -- * Computation
, (<#>)
, (<&>)
, (<&)
, liftP2
, pair
  -- * Documents
, Doc(..)
  -- * Exponentials
, type (-->)(..)
  -- * Coexponentials
, type (>--)(..)
, (>--)
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
  p1 <> p2 = printer (\ k a -> appPrint p1 a (\ a' -> appPrint p2 a (lmap (mappend a') k)))

instance Monoid (Printer a) where
  mempty = Printer (constK . (• mempty))

instance Print (Printer a) where
  char c = Printer (constK . (• char c))
  string s = Printer (constK . (• string s))

instance Contravariant Printer where
  contramap f (Printer r) = Printer (lmap f . r)


-- Construction

printer :: (forall r . (Doc -> r) -> (a -> r)) -> Printer a
printer f = Printer (K . f . (•))

withSubject :: (a -> Printer a) -> Printer a
withSubject f = printer (\ k a -> appPrint (f a) a k)

contrapure :: (b -> a) -> Printer (a >-- b)
contrapure f = printer (\ k (pa :>-- b) -> appPrint pa (f b) k)


-- Elimination

print :: Printer a -> a -> Doc
print p = (runPrint p idK •)

appPrint :: Printer a -> a -> (Doc -> r) -> r
appPrint p a k = runPrint p (K k) • a


-- Computation

(<#>) :: (b >-- a) -> Printer a -> Printer b
f <#> a = printer (\ k b -> appPrint a (coconst f) (\ a -> appPrint (coK f) b (k . mappend a)))

infixl 4 <#>

(<&>) :: Printer (a >-- b) -> Printer a -> Printer b
pf <&> pa = printer (\ k b -> appPrint pf (pa >-- b) k)

infixl 4 <&>

(<&) :: Printer a -> Printer b -> Printer a
a <& b = contramap coconst a <&> b

infixl 4 <&

liftP2 :: ((b >-- c) >-- a) -> Printer a -> Printer b -> Printer c
liftP2 f a b = f <#> a <&> b

pair :: Printer a -> Printer b -> Printer (a, b)
pair a b = pairP <&> a <&> b

pairP :: Printer (a >-- b >-- (a, b))
pairP = printer (\ k (pa :>-- pb :>-- (a, b)) ->
  appPrint pa a (appPrint pb b . (k .) . pairD))
  where
  pairD da db = parens (da <> comma <+> db)


-- Documents

newtype Doc = Doc { getDoc :: ShowS }
  deriving (Monoid, Semigroup) via Endo String

instance Print Doc where
  char c = Doc (c:)
  string s = Doc (s<>)


-- Exponentials

newtype a --> b = F { runF :: forall r . b • r -> a • r }

instance Profunctor (-->) where
  dimap f g (F r) = F (dimap (lmap g) (lmap f) r)

instance Functor ((-->) a) where
  fmap = rmap


-- Coexponentials

data a >-- b = Printer a :>-- b
  deriving (Functor)

infixr 0 >--, :>--

instance Profunctor (>--) where
  dimap f g (a :>-- b) = contramap f a >-- g b


(>--) :: Printer a -> b -> a >-- b
(>--) = (:>--)


coK :: (a >-- b) -> Printer a
coK (k :>-- _) = k

coconst :: (a >-- b) -> b
coconst (_ :>-- a) = a

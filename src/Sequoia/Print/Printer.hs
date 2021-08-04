-- | Pretty-printing.
module Sequoia.Print.Printer
( -- * Printers
  Printer(..)
  -- * Construction
, printer
  -- * Elimination
, print
  -- * Computation
, (<&>)
, pair
  -- * Documents
, Doc(..)
  -- * Coexponentials
, type (>-)(..)
, (>-)
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

printer :: (a -> Printer a) -> Printer a
printer f = Printer (\ k -> K (\ a -> runPrint (f a) k • a))


-- Elimination

print :: Printer a -> a -> Doc
print p = (runPrint p idK •)


-- Computation

(<&>) :: Printer (a >- b) -> Printer a -> Printer b
pf <&> pa = Printer (\ k -> K (\ b -> runPrint pf k • (pa >- b)))

infixl 4 <&>

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

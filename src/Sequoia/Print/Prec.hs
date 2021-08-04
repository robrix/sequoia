module Sequoia.Print.Prec
( -- * Precedence printing
  Prec(..)
, PrecPrinter(..)
  -- * Construction
, prec
, atom
  -- * Elimination
, withPrec
) where

import Data.Functor.Contravariant
import Sequoia.Print.Class

-- Precedence printing

newtype Prec = Prec { getPrec :: Int }
  deriving (Eq, Ord, Show)

newtype PrecPrinter p a = PrecPrinter { runPrecPrinter :: Prec -> p a }
  deriving (Functor)

instance Contravariant p => Contravariant (PrecPrinter p) where
  contramap f (PrecPrinter r) = PrecPrinter (contramap f . r)


-- Construction

prec :: Print (p a) => Prec -> p a -> PrecPrinter p a
prec i pr = PrecPrinter $ \ i' -> parensIf (i' > i) pr

atom :: p a -> PrecPrinter p a
atom = PrecPrinter . const


-- Elimination

withPrec :: Prec -> PrecPrinter p a -> p a
withPrec = flip runPrecPrinter

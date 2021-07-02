-- | Pretty-printing.
module Focalized.Printer
( Doc(..)
, printer
, Printer(..)
, prec
, atom
, withPrec
, Prec(..)
, PrecPrinter(..)
, Print(..)
) where

import Data.Functor.Contravariant
import Data.Monoid (Endo(..))

newtype Doc = Doc { getDoc :: ShowS }
  deriving (Monoid, Semigroup) via Endo String

instance Print Doc where
  char c = Doc (c:)
  string s = Doc (s<>)


printer :: (forall x . a -> Printer x) -> Printer a
printer f = Printer (runPrinter . f <*> id)

newtype Printer a = Printer { runPrinter :: a -> Doc }
  deriving (Monoid, Semigroup)

instance Contravariant Printer where
  contramap f (Printer r) = Printer (r . f)

instance Print (Printer a) where
  char c = Printer (const (Doc (c:)))
  string s = Printer (const (Doc (s<>)))


prec :: Print (p a) => Prec -> p a -> PrecPrinter p a
prec i pr = PrecPrinter $ \ i' -> parensIf (i' > i) pr

atom :: p a -> PrecPrinter p a
atom = PrecPrinter . const

withPrec :: Prec -> PrecPrinter p a -> p a
withPrec = flip runPrecPrinter

newtype Prec = Prec { getPrec :: Int }
  deriving (Eq, Ord, Show)

newtype PrecPrinter p a = PrecPrinter { runPrecPrinter :: Prec -> p a }
  deriving (Functor)

instance Contravariant p => Contravariant (PrecPrinter p) where
  contramap f (PrecPrinter r) = PrecPrinter (contramap f . r)


parensIf :: Print p => Bool -> p -> p
parensIf True  = parens
parensIf False = id

class Monoid p => Print p where
  {-# MINIMAL char | string #-}
  char :: Char -> p
  char c = string [c]
  string :: String -> p
  string = foldMap char

  lparen, rparen :: p
  lparen = char '('
  rparen = char ')'

  surround :: p -> p -> p -> p
  surround l r x = l <> x <> r

  parens :: p -> p
  parens = surround lparen rparen

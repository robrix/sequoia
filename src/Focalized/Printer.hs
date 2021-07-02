-- | Pretty-printing.
module Focalized.Printer
( Printer(..)
, Prec(..)
, PrecPrinter(..)
) where

newtype Printer a = Printer { runPrinter :: a -> ShowS }


newtype Prec = Prec { getPrec :: Int }

newtype PrecPrinter p a = PrecPrinter { runPrecPrinter :: Prec -> p a }

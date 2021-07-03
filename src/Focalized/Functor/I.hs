module Focalized.Functor.I
( -- Identity functor
  I(..)
) where

newtype I a = I { getI :: a }

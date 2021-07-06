module Sequoia.Value
( Value
) where

import Data.Functor.Rep

class Representable v => Value v

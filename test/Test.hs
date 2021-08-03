module Main
( main
) where

import           Hedgehog.Main
import qualified Cons.Test
import qualified Line.Test

main :: IO ()
main = defaultMain
  [ Cons.Test.tests
  , Line.Test.tests
  ]

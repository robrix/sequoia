module Main
( main
) where

import           Hedgehog.Main
import qualified Sequoia.Cons.Test
import qualified Sequoia.Line.Test

main :: IO ()
main = defaultMain
  [ Sequoia.Cons.Test.tests
  , Sequoia.Line.Test.tests
  ]

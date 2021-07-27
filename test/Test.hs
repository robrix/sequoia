module Main
( main
) where

import           Hedgehog.Main
import qualified Sequoia.Line.Test
import qualified Sequoia.List.Test

main :: IO ()
main = defaultMain
  [ Sequoia.Line.Test.tests
  , Sequoia.List.Test.tests
  ]

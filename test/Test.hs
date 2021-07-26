module Main
( main
) where

import           Hedgehog.Main
import qualified Sequoia.List.Test

main :: IO ()
main = defaultMain
  [ Sequoia.List.Test.tests
  ]

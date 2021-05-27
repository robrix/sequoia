module Main
( main
) where

import qualified Focalized.Multiset.Test
import           Hedgehog.Main

main :: IO ()
main = defaultMain
  [ Focalized.Multiset.Test.tests
  ]

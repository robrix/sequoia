{-# LANGUAGE TemplateHaskell #-}
module Focalized.Multiset.Test
( tests
) where

import Hedgehog

tests :: IO Bool
tests = checkParallel $$(discover)

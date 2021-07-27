{-# LANGUAGE TemplateHaskell #-}
module Sequoia.Line.Test
( tests
) where

import Hedgehog

tests :: IO Bool
tests = checkParallel $$(discover)

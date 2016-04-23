module Main where

import Test.Tasty

import qualified Suites.Parser

main :: IO ()
main = defaultMain $ testGroup "fffuu"
  [ Suites.Parser.tests
  ]

module Suites.FffuuBinary ( tests ) where

import Test.Tasty
import Test.Tasty.Golden as Golden
import qualified Data.ByteString.Lazy.Char8 as B


test_fffuu_help = Golden.goldenVsString "run fffuu" "test/Suites/GoldenFiles/help" $ do
    return $ B.pack "this fails"

tests = testGroup "fffuu compiled binary output" $
  [ test_fffuu_help
  ]

module Suites.FffuuBinary ( tests ) where

import Test.Tasty
import Test.Tasty.Golden as Golden
import qualified Data.ByteString.Lazy.Char8 as B
import System.Process (readProcess)

diffCmd = \ref new -> ["/usr/bin/diff", "-u", ref, new]
fffuuBin = "./dist/build/fffuu/fffuu"

--goldenVsString
test_fffuu_help = Golden.goldenVsStringDiff "run fffuu" diffCmd "test/Suites/GoldenFiles/help" $ do
    outp <- readProcess fffuuBin ["--help"] ""
    return $ B.pack outp

tests = testGroup "fffuu compiled binary output" $
  [ test_fffuu_help
  ]

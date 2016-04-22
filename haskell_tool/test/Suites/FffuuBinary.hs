module Suites.FffuuBinary ( tests ) where

import Data.List (intercalate)
import Test.Tasty
import Test.Tasty.Golden as Golden
import qualified Data.ByteString.Lazy.Char8 as B
import System.Process (readProcess)



execFffuu :: TestName
             -> [String] -- command line argument for fffuu
             -> FilePath -- path to the golden file (expected output)
             -> TestTree
execFffuu name argv goldenFile = Golden.goldenVsStringDiff fancyName diffCmd goldenFile $ do
    outp <- readProcess fffuuBin argv ""
    return $ B.pack outp
    where diffCmd = \ref new -> ["/usr/bin/diff", "-u", ref, new]
          fffuuBin = "./dist/build/fffuu/fffuu"
          fancyName = name ++ ": " ++ fffuuBin ++ " " ++ intercalate " " argv

test_fffuu_help = execFffuu "help" ["--help"] "test/Suites/GoldenFiles/help"

tests = testGroup "fffuu compiled binary output" $
  [ test_fffuu_help
  ]

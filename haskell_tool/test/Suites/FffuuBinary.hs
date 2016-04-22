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
          fancyName = name ++ ": `" ++ fffuuBin ++ " " ++ (intercalate " " argv) ++ "`"


tests = testGroup "fffuu compiled binary output" $
  [ execFffuu "help" ["--help"] "test/Suites/GoldenFiles/help"
  , execFffuu "help" ["../thy/Examples/Parser_Test/data/iptables-save"] "test/Suites/GoldenFiles/parser_test"
  , execFffuu "help" ["--ipassmt", "ipassmt_tumi8", "../thy/Examples/TUM_Net_Firewall/iptables-save-2015-05-15_15-23-41_cheating"] "test/Suites/GoldenFiles/i8_iptables-save-2015-05-15_15-23-41_cheating"
  ]

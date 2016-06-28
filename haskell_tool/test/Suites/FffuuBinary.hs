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
  , execFffuu "stressing the parser" ["--verbose", "../thy/Iptables_Semantics/Examples/Parser_Test/data/iptables-save"] "test/Suites/GoldenFiles/parser_test"
  , execFffuu "i8 with spoofing protection" ["--ipassmt", "ipassmt_tumi8", "../thy/Iptables_Semantics/Examples/TUM_Net_Firewall/iptables-save-2015-05-15_15-23-41_cheating"] "test/Suites/GoldenFiles/i8_iptables-save-2015-05-15_15-23-41_cheating"
  , execFffuu "SQRL spoofing raw" ["--verbose", "--table", "raw", "--chain", "PREROUTING", "--ipassmt", "ipassmt_sqrl", "../thy/Iptables_Semantics/Examples/SQRL_Shorewall/2015_aug_iptables-save-spoofing-protection"] "test/Suites/GoldenFiles/sqrl_2015_aug_iptables-save-spoofing-protection"
  , execFffuu "synology example from README" ["--verbose", "--chain", "INPUT", "--service_matrix_dport", "22", "--service_matrix_dport", "8080", "--service_matrix_dport", "80", "../thy/Iptables_Semantics/Examples/Synology_Diskstation_DS414/iptables-save_jun_2015_cleanup"] "test/Suites/GoldenFiles/synology_iptables-save_jun_2015_cleanup"
  ]

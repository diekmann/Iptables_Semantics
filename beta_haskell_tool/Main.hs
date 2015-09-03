module Main where

import qualified System.Environment
import Network.IPTables.Ruleset
import Network.IPTables.Parser
import Network.IPTables.IpassmtParser
import qualified Data.Map as M
import qualified Data.List as L

import qualified Network.IPTables.Generated as Isabelle


preprocessForSpoofingProtection unfolded = Isabelle.upper_closure $ Isabelle.ctstate_assume_new unfolded

exampleCertSpoof ipassmt fuc = map (\ifce -> (ifce, Isabelle.no_spoofing_iface ifce ipassmtMap fuc)) interfaces
    where interfaces = map fst ipassmt
          ipassmtMap = Isabelle.map_of_ipassmt ipassmt

readIpAssmt filename = do
    src <- readFile filename
    case parseIpAssmt filename src of
        Left err -> do print err
                       error $ "could not parse " ++ filename
        Right res -> do putStrLn "Parsed IpAssmt"
                        putStrLn (show res)
                        return $ ipAssmtToIsabelle res


getIpAssmt = do
    args <- System.Environment.getArgs
    progName <- System.Environment.getProgName
    case length args of
      0 -> do putStrLn "no argument supplied"
              putStrLn "for the sake of example, I'm loading TUM_i8_ipassmt"
              putStrLn "Probably, this makes no sense!"
              return (Isabelle.example_TUM_i8_spoofing_ipassmt)
      1 -> do putStrLn $ "loading ipassmt from `" ++ filename ++ "'"
              readIpAssmt filename
                  where filename = head args
      _ -> do putStrLn $ "Usage: " ++ progName ++ " ipassmt_file"
              error "too many command line parameters"

-- TODO: command line parameter handling
-- select table and chain

main = do
    ipassmt <- getIpAssmt
    src <- getContents
    case parseIptablesSave "<stdin>" src of
        Left err -> print err
        Right res -> do
            putStrLn $ "== Parser output =="
            putStrLn $ show res
            putStrLn "== Checking which tables are supported for analysis. Usually, only `filter'. =="
            checkParsedTables res
            putStrLn "== Transformed to Isabelle type (only filter table) =="
            let (fw, defaultPolicies) = rulesetLookup "filter" res
            let Just policy_FORWARD = M.lookup "FORWARD" defaultPolicies
            putStrLn $ show $ fw
            putStrLn $ show $ "Default Policies: " ++ show defaultPolicies
            putStrLn "== unfolded FORWARD chain =="
            let unfolded = Isabelle.unfold_ruleset_FORWARD (policy_FORWARD) $ Isabelle.map_of_string (Isabelle.rewrite_Goto fw)
            putStrLn $ L.intercalate "\n" $ map show unfolded
            putStrLn "== unfolded FORWARD chain (upper closure) =="
            putStrLn $ L.intercalate "\n" $ map show (Isabelle.upper_closure $ unfolded)
            putStrLn "== to simple firewall =="
            putStrLn $ L.intercalate "\n" $ map show (Isabelle.to_simple_firewall $ Isabelle.upper_closure $ Isabelle.optimize_matches Isabelle.abstract_for_simple_firewall $ Isabelle.ctstate_assume_new $ unfolded)
            putStrLn "== to even-simpler firewall =="
            putStrLn $ L.intercalate "\n" $ map show (Isabelle.to_simple_firewall_without_interfaces unfolded)
            putStrLn "== checking spoofing protection =="
            let fuc = preprocessForSpoofingProtection unfolded --Firewall Under Certification
            --putStrLn $ show fuc
            putStrLn $ "ipassmt_sanity_defined: " ++ show (Isabelle.ipassmt_sanity_defined fuc (Isabelle.map_of_ipassmt ipassmt))
            mapM_  (putStrLn . show) (exampleCertSpoof ipassmt fuc)
            return ()

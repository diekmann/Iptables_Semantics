module Main where

import Text.Parsec

import Network.IPTables.Ruleset
import Network.IPTables.Parser
import qualified Data.Map as M
import qualified Data.List as L

import qualified Network.IPTables.Generated as Isabelle


main = do
    src <- getContents
    case runParser ruleset initRState "<stdin>" src of
        Left err -> print err
        Right res -> do
            putStrLn $ "-- Parser output --"
            putStrLn $ show res
            putStrLn "-- Transformed to Isabelle type (only filter table) --"
            let (fw, defaultPolicies) = rulesetLookup "filter" res
            let Just policy_FORWARD = M.lookup "FORWARD" defaultPolicies
            putStrLn $ show $ fw
            putStrLn $ show $ "Default Policies: " ++ show defaultPolicies
            putStrLn "-- unfolded FORWARD chain --"
            let unfolded = Isabelle.unfold_ruleset_FORWARD (policy_FORWARD) $ Isabelle.map_of_string (Isabelle.rewrite_Goto fw)
            putStrLn $ L.intercalate "\n" $ map show unfolded
            putStrLn "-- unfolded FORWARD chain (uper closure) --"
            putStrLn $ L.intercalate "\n" $ map show (Isabelle.upper_closure $ unfolded)
            putStrLn "-- to simple firewall --"
            putStrLn $ L.intercalate "\n" $ map show (Isabelle.to_simple_firewall $ Isabelle.upper_closure $ Isabelle.optimize_matches Isabelle.abstract_for_simple_firewall $ Isabelle.ctstate_assume_new $ unfolded)
            putStrLn "-- to even-simpler firewall --"
            putStrLn $ L.intercalate "\n" $ map show (Isabelle.to_simple_firewall_without_interfaces unfolded)
            return ()

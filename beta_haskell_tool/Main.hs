module Main where

import Text.Parsec

import Network.IPTables.Ruleset
import Network.IPTables.Parser
import qualified Data.Map as M
import qualified Data.List as L
import qualified Debug.Trace
import qualified Control.Exception

import qualified Network.IPTables.Generated as Isabelle



    
instance Show Isabelle.Iface where
    show (Isabelle.Iface i) = i

preprocessForSpoofingProtection unfolded = Isabelle.upper_closure $ Isabelle.ctstate_assume_new unfolded

exampleCertSpoof fuc = map (\ifce -> (ifce, Isabelle.no_spoofing_iface ifce ipassmt fuc)) interfaces
    where interfaces = map fst Isabelle.example_TUM_i8_spoofing_ipassmt
          ipassmt = Isabelle.map_of_ipassmt Isabelle.example_TUM_i8_spoofing_ipassmt

--TODO: find a good way to check this
-- this is just DEBUG
checkParsedTables res = map (\table -> Debug.Trace.trace ("sanity check for table: " ++ table) (check table res)) tables
    where tables = M.keys (rsetTables res)
          check table res = Control.Exception.catch (putStrLn (show (rulesetLookup table res))) (\msg -> putStrLn $ "caught " ++ show (msg::Control.Exception.SomeException))

             
main = do
    src <- getContents
    case runParser ruleset initRState "<stdin>" src of
        Left err -> print err
        Right res -> do
            putStrLn $ "-- Parser output --"
            putStrLn $ show res
            _ <- Debug.Trace.trace "sanity checks" (sequence (checkParsedTables res))
            putStrLn "-- Transformed to Isabelle type (only filter table) --"
            let (fw, defaultPolicies) = rulesetLookup "filter" res
            let Just policy_FORWARD = M.lookup "FORWARD" defaultPolicies
            putStrLn $ show $ fw
            putStrLn $ show $ "Default Policies: " ++ show defaultPolicies
            putStrLn "-- unfolded FORWARD chain --"
            let unfolded = Isabelle.unfold_ruleset_FORWARD (policy_FORWARD) $ Isabelle.map_of_string (Isabelle.rewrite_Goto fw)
            --putStrLn $ L.intercalate "\n" $ map show unfolded
            putStrLn "-- unfolded FORWARD chain (upper closure) --"
            --putStrLn $ L.intercalate "\n" $ map show (Isabelle.upper_closure $ unfolded)
            putStrLn "-- to simple firewall --"
            --putStrLn $ L.intercalate "\n" $ map show (Isabelle.to_simple_firewall $ Isabelle.upper_closure $ Isabelle.optimize_matches Isabelle.abstract_for_simple_firewall $ Isabelle.ctstate_assume_new $ unfolded)
            putStrLn "-- to even-simpler firewall --"
            --putStrLn $ L.intercalate "\n" $ map show (Isabelle.to_simple_firewall_without_interfaces unfolded)
            putStrLn "-- checking spoofing protection (for the hard-coded example_TUM_i8_spoofing_ipassmt) --"
            let fuc = preprocessForSpoofingProtection unfolded -- Firewall Unter Certification
            --putStrLn $ show fuc
            putStrLn $ "ipassmt_sanity_defined: " ++ show (Isabelle.ipassmt_sanity_defined fuc (Isabelle.map_of_ipassmt Isabelle.example_TUM_i8_spoofing_ipassmt))
            mapM_  (putStrLn . show) (exampleCertSpoof fuc)
            return ()

module Network.IPTables.Analysis
( toSimpleFirewall
, toSimpleFirewallWithoutInterfaces
, certifySpoofingProtection
)
where

import qualified Data.List as L
import Network.IPTables.Ruleset -- show instances
import Network.IPTables.IpassmtParser (IsabelleIpAssmt) --nicer type --TODO: move?

import qualified Network.IPTables.Generated as Isabelle

preprocessForSpoofingProtection = Isabelle.upper_closure . Isabelle.ctstate_assume_new

exampleCertSpoof ipassmt fuc = map (\ifce -> (ifce, Isabelle.no_spoofing_iface ifce ipassmtMap fuc)) interfaces
    where interfaces = map fst ipassmt
          ipassmtMap = Isabelle.map_of_ipassmt ipassmt


-- TODO: check if this call is currently the best optimized one in the thy
-- TODO: export code directly from the and have correctness thm linked here
toSimpleFirewall :: [Isabelle.Rule Isabelle.Common_primitive] -> [Isabelle.Simple_rule]
toSimpleFirewall = Isabelle.to_simple_firewall . Isabelle.upper_closure . 
                         Isabelle.optimize_matches Isabelle.abstract_for_simple_firewall .
                           Isabelle.ctstate_assume_new 

toSimpleFirewallWithoutInterfaces :: IsabelleIpAssmt -> [Isabelle.Rule Isabelle.Common_primitive] -> [Isabelle.Simple_rule]
toSimpleFirewallWithoutInterfaces = Isabelle.to_simple_firewall_without_interfaces


-- ipassmt -> rs -> (warning_and_debug, spoofing_certification_results)
certifySpoofingProtection :: IsabelleIpAssmt -> [Isabelle.Rule Isabelle.Common_primitive] -> ([String], [(Isabelle.Iface, Bool)])
certifySpoofingProtection ipassmt rs = (warn_defined ++ debug_ipassmt, certResult)
    where -- fuc: firewall under certification, prepocessed (debug functions need nnf-normalized match expressions)
          fuc = Isabelle.upper_closure $ Isabelle.ctstate_assume_new rs
          warn_defined = if (Isabelle.ipassmt_sanity_defined fuc ipassmtMap)
                         then []
                         else ["WARNING There are some interfaces in your firewall ruleset which are not defined in your ipassmt."]
          debug_ipassmt = Isabelle.debug_ipassmt ipassmt fuc
          ipassmtMap = Isabelle.map_of_ipassmt ipassmt
          certResult = map (\ifce -> (ifce, Isabelle.no_spoofing_iface ifce ipassmtMap fuc)) interfaces
              where interfaces = map fst ipassmt




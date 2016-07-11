module Network.IPTables.Analysis
( toSimpleFirewall
, toSimpleFirewallWithoutInterfaces
, certifySpoofingProtection_ipv4
, certifySpoofingProtection_ipv6
, accessMatrix_ipv4
, accessMatrix_ipv6
)
where

--import Network.IPTables.Ruleset -- show instances
import Network.IPTables.IsabelleToString (Word32, Word128)
import Network.IPTables.IpassmtParser (IsabelleIpAssmt) --nicer type --TODO: move?

import qualified Network.IPTables.Generated as Isabelle


-- checks that the simple_firewall has a default rule. Not having a default rule
-- is not actually an assumption required by the theorems but it would indicate
-- a broken parser
-- Throws an exception
check_simpleFw_sanity
    :: Isabelle.Len a => [Isabelle.Simple_rule a] -> [Isabelle.Simple_rule a]
check_simpleFw_sanity rs =
    if 
        not (Isabelle.has_default_policy rs)
    then
        error "simple firewall does not have a default rule!"
    else if
        not (Isabelle.sanity_check_simple_firewall rs)
    then
        error "something went wrong with the simple firewall (matching on port numbers without a protocol)"
    else
        rs


-- all functions must only be called with a simple_ruleset. TODO: check this?


-- Theorem: new_packets_to_simple_firewall_overapproximation
toSimpleFirewall
    :: Isabelle.Len a => [Isabelle.Rule (Isabelle.Common_primitive a)] -> [Isabelle.Simple_rule a]
toSimpleFirewall = check_simpleFw_sanity . 
                        Isabelle.to_simple_firewall . Isabelle.upper_closure . 
                            Isabelle.optimize_matches Isabelle.abstract_for_simple_firewall .
                                Isabelle.upper_closure . Isabelle.packet_assume_new 

-- Theorem: to_simple_firewall_without_interfaces
toSimpleFirewallWithoutInterfaces
    :: Isabelle.Len a => IsabelleIpAssmt a -> [Isabelle.Rule (Isabelle.Common_primitive a)] -> [Isabelle.Simple_rule a]
toSimpleFirewallWithoutInterfaces ipassmt = check_simpleFw_sanity . Isabelle.to_simple_firewall_without_interfaces ipassmt


-- Theorem: no_spoofing_executable_set
-- ipassmt -> rs -> (warning_and_debug, spoofing_certification_results)
certifySpoofingProtection_generic 
    :: Isabelle.Len a =>
        (IsabelleIpAssmt a -> [Isabelle.Rule (Isabelle.Common_primitive a)] -> [String])
         -> IsabelleIpAssmt a -> [Isabelle.Rule (Isabelle.Common_primitive a)] -> ([String], [(Isabelle.Iface, Bool)])
certifySpoofingProtection_generic debug_ipassmt_f ipassmt rs = (warn_defined ++ debug_ipassmt, certResult)
    where -- fuc: firewall under certification, prepocessed
          -- no_spoofing_executable_set requires normalized_nnf_match. Isabelle.upper_closure guarantees this.
          -- It also guarantees that if we start from a simple_ruleset, it remains a simple ruleset.
          -- Theorem: no_spoofing_executable_set_preprocessed
          fuc = Isabelle.upper_closure $ Isabelle.packet_assume_new rs
          warn_defined = if (Isabelle.ipassmt_sanity_defined fuc ipassmtMap) -- fuc needs to be nnf-normalized
                         then []
                         else ["WARNING There are some interfaces in your firewall ruleset which are not defined in your ipassmt."]
          debug_ipassmt = debug_ipassmt_f ipassmt fuc
          ipassmtMap = Isabelle.map_of_ipassmt ipassmt
          certResult = map (\ifce -> (ifce, Isabelle.no_spoofing_iface ifce ipassmtMap fuc)) interfaces
              where interfaces = map fst ipassmt

certifySpoofingProtection_ipv4 :: IsabelleIpAssmt Word32 -> [Isabelle.Rule (Isabelle.Common_primitive Word32)] -> ([String], [(Isabelle.Iface, Bool)])
certifySpoofingProtection_ipv4 = certifySpoofingProtection_generic Isabelle.debug_ipassmt_ipv4

certifySpoofingProtection_ipv6 :: IsabelleIpAssmt Word128 -> [Isabelle.Rule (Isabelle.Common_primitive Word128)] -> ([String], [(Isabelle.Iface, Bool)])
certifySpoofingProtection_ipv6 = certifySpoofingProtection_generic Isabelle.debug_ipassmt_ipv6


-- Theorem: access_matrix
-- TODO: in Main.hs we directly have upper_simple available. Make a specific function which gets upper_simple?
-- This is slightly faster (tested!) but dangerously because someone might call it wrong (e.g. with a firewall with interfaces)
--accessMatrix_generic :: IsabelleIpAssmt Word32 -> [Isabelle.Rule (Isabelle.Common_primitive Word32)] -> Integer -> Integer -> ([(String, String)], [(String, String)])
accessMatrix_generic access_matrix_pretty ipassmt rs sport dport = if sport >= 65536 || dport >= 65536 then error "ports are 16 bit"
    -- Theorem: access_matrix
    else access_matrix_pretty parts_connection upper_simple
    -- Theorem: to_simple_firewall_without_interfaces
    where upper_simple = toSimpleFirewallWithoutInterfaces ipassmt rs
          parts_connection = Isabelle.mk_parts_connection_TCP (Isabelle.integer_to_16word sport) (Isabelle.integer_to_16word dport)

accessMatrix_ipv4 :: IsabelleIpAssmt Word32 -> [Isabelle.Rule (Isabelle.Common_primitive Word32)] -> Integer -> Integer -> ([(String, String)], [(String, String)])
accessMatrix_ipv4 = accessMatrix_generic Isabelle.access_matrix_pretty_ipv4

accessMatrix_ipv6 :: IsabelleIpAssmt Word128 -> [Isabelle.Rule (Isabelle.Common_primitive Word128)] -> Integer -> Integer -> ([(String, String)], [(String, String)])
accessMatrix_ipv6 = accessMatrix_generic Isabelle.access_matrix_pretty_ipv6


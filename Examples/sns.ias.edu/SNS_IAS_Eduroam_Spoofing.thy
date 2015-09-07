theory SNS_IAS_Eduroam_Spoofing
imports 
  "../../Primitive_Matchers/Parser"
  "../../Simple_Firewall/SimpleFw_toString"
begin


section{*Example: Eduroam and sns.ias Firewall Script*}

definition "everything_but_my_ip = all_but_those_ips [(ipv4addr_of_dotdecimal (131,159,207,206), 32)]"


text{* Incoming: everything but my IP *}
definition "ipassignment_incoming = [(Iface ''wlan0'', everything_but_my_ip), (Iface ''lo'', [(0,0)])]"

lemma "ipassmt_sanity_nowildcards (map_of ipassignment_incoming)" by eval

text{* Outgoing: only my IP *}
definition "ipassignment_outgoing = [(Iface ''wlan0'',  [(ipv4addr_of_dotdecimal (131,159,207,206), 32)]), (Iface ''lo'', [(0,0)])]"

lemma "ipassmt_sanity_nowildcards (map_of ipassignment_outgoing)" by eval

parse_iptables_save eduroam_fw="eduroam_iptables-save"

thm eduroam_fw_def
thm eduroam_fw_INPUT_default_policy_def

value[code] "debug_ipassmt ipassignment_incoming (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw))"

value[code] "unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw)"

value[code] "collect_ifaces (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw))"


lemma "ipassmt_sanity_defined (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw)) (map_of_ipassmt ipassignment_incoming)" by eval
lemma "ipassmt_sanity_defined (unfold_ruleset_OUTPUT eduroam_fw_OUTPUT_default_policy (map_of_string eduroam_fw)) (map_of_ipassmt ipassignment_outgoing)" by eval

text{*The ruleset*}

value[code] "map simple_rule_toString (to_simple_firewall (ctstate_assume_new 
                  (upper_closure (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw)))))"

text{*We do not need to call things such as @{const transform_optimize_dnf_strict} because the
     firewall already is in @{const normalized_nnf_match} (required for @{const no_spoofing_iface})*}
lemma "transform_optimize_dnf_strict (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw)) =
          unfold_ruleset_INPUT action.Drop (map_of_string eduroam_fw)" by eval

text{* The ruleset prevents spoofed incoming packets *}
lemma "no_spoofing_iface (Iface ''wlan0'')
        (map_of_ipassmt ipassignment_incoming) (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw))" by eval


text{*Ruleset does not prevent that I'm spoofing (which is not necessary anyways since I need root right to spoof, which 
      would also enable me to deactivate the firewall). This is only a one-user laptop!*}

lemma "transform_optimize_dnf_strict (unfold_ruleset_OUTPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw)) =
        unfold_ruleset_OUTPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw)" by eval

lemma "\<not> no_spoofing_iface (Iface ''wlan0'')
        (map_of_ipassmt ipassignment_outgoing) (unfold_ruleset_OUTPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw))" by eval


end
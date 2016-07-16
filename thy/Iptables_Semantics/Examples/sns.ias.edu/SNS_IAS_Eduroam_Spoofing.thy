theory SNS_IAS_Eduroam_Spoofing
imports 
  "../../Primitive_Matchers/Parser"
begin


section\<open>Example: Eduroam and sns.ias Firewall Script\<close>

definition "everything_but_my_ip = all_but_those_ips [(ipv4addr_of_dotdecimal (131,159,207,206), 32)]"


text\<open>Incoming: everything but my IP\<close>
definition "ipassignment_incoming = [(Iface ''wlan0'', everything_but_my_ip), (Iface ''lo'', [(0,0)])]"

lemma "ipassmt_sanity_nowildcards (map_of ipassignment_incoming)" by eval

text\<open>Outgoing: only my IP\<close>
definition "ipassignment_outgoing = [(Iface ''wlan0'',  [(ipv4addr_of_dotdecimal (131,159,207,206), 32)]), (Iface ''lo'', [(0,0)])]"

lemma "ipassmt_sanity_nowildcards (map_of ipassignment_outgoing)" by eval

parse_iptables_save eduroam_fw="eduroam_iptables-save"

thm eduroam_fw_def
thm eduroam_fw_INPUT_default_policy_def

value[code] "debug_ipassmt_ipv4 ipassignment_incoming (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string_ipv4 eduroam_fw))"

value[code] "unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string_ipv4 eduroam_fw)"

value[code] "collect_ifaces (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string_ipv4 eduroam_fw))"


lemma "ipassmt_sanity_defined (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string_ipv4 eduroam_fw)) (map_of_ipassmt ipassignment_incoming)" by eval
lemma "ipassmt_sanity_defined (unfold_ruleset_OUTPUT eduroam_fw_OUTPUT_default_policy (map_of_string_ipv4 eduroam_fw)) (map_of_ipassmt ipassignment_outgoing)" by eval


value[code] "debug_ipassmt_ipv4 ipassignment_incoming (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string_ipv4 eduroam_fw))"
value[code] "debug_ipassmt_ipv4 ipassignment_outgoing (unfold_ruleset_OUTPUT eduroam_fw_OUTPUT_default_policy (map_of_string_ipv4 eduroam_fw))"


text\<open>The ruleset\<close>
lemma "check_simple_fw_preconditions (upper_closure (packet_assume_new (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string_ipv4 eduroam_fw))))" by eval
value[code] "map simple_rule_ipv4_toString (to_simple_firewall (upper_closure (packet_assume_new (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string_ipv4 eduroam_fw)))))"
lemma "simple_fw_valid (to_simple_firewall (upper_closure (packet_assume_new (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string_ipv4 eduroam_fw)))))" by eval
lemma "simple_fw_valid (to_simple_firewall (lower_closure (packet_assume_new (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string_ipv4 eduroam_fw)))))" by eval


text\<open>We do not need to call things such as @{const transform_optimize_dnf_strict} because the
     firewall already is in @{const normalized_nnf_match} (required for @{const no_spoofing_iface})\<close>
lemma "transform_optimize_dnf_strict (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string_ipv4 eduroam_fw)) =
          unfold_ruleset_INPUT action.Drop (map_of_string_ipv4 eduroam_fw)" by eval

text\<open>The ruleset prevents spoofed incoming packets\<close>
lemma "no_spoofing_iface (Iface ''wlan0'')
        (map_of_ipassmt ipassignment_incoming) (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string_ipv4 eduroam_fw))" by eval


text\<open>Ruleset does not prevent that I'm spoofing (which is not necessary anyways since I need root right to spoof, which 
      would also enable me to deactivate the firewall). This is only a one-user laptop!\<close>

lemma "transform_optimize_dnf_strict (unfold_ruleset_OUTPUT eduroam_fw_INPUT_default_policy (map_of_string_ipv4 eduroam_fw)) =
        unfold_ruleset_OUTPUT eduroam_fw_INPUT_default_policy (map_of_string_ipv4 eduroam_fw)" by eval

lemma "\<not> no_spoofing_iface (Iface ''wlan0'')
        (map_of_ipassmt ipassignment_outgoing) (unfold_ruleset_OUTPUT eduroam_fw_INPUT_default_policy (map_of_string_ipv4 eduroam_fw))" by eval


end
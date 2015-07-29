theory SNS_IAS_Eduroam_Spoofing
imports "../Code_Interface"
  "../../Primitive_Matchers/No_Spoof"
  "../Parser"
begin


section{*Example: Eduroam and sns.ias Firewall Script*}


definition "everything_but_my_ip = ipv4range_split (ipv4range_invert (ipv4_cidr_tuple_to_interval (ipv4addr_of_dotdecimal (131,159,207,206), 32)))"


text{*This is really the range of everything but my IP*}
lemma "ipv4cidr_union_set (set everything_but_my_ip) = UNIV - ipv4range_set_from_bitmask (ipv4addr_of_dotdecimal (131,159,207,206)) 32"
  apply(simp add: ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)
  unfolding ipv4cidr_union_set_def everything_but_my_ip_def
  apply(simp)
  apply(simp add: ipv4range_split_bitmask[simplified])
  apply(simp add: ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)
  apply(simp add: ipv4range_invert_def ipv4range_setminus_def)
  apply(simp add: ipv4range_to_set_ipv4_cidr_tuple_to_interval[simplified ipv4range_to_set_def])
  apply(simp add: ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)
  apply(simp add: ipv4range_UNIV_def)
  done


text{* Incoming: everything but my IP *}
definition "ipassignment_incoming = ([Iface ''wlan0'' \<mapsto> everything_but_my_ip]:: ipassignment)"

text{* Outgoing: only my IP *}
definition "ipassignment_outgoing = ([Iface ''wlan0'' \<mapsto> [(ipv4addr_of_dotdecimal (131,159,207,206), 32)]]:: ipassignment)"


parse_iptables_save eduroam_fw="eduroam_iptables-save"

thm eduroam_fw_def
thm eduroam_fw_INPUT_default_policy_def

value[code] "unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw)"

text{*The ruleset*}

value[code] "map simple_rule_toString (to_simple_firewall (ctstate_assume_new 
                  (upper_closure (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw)))))"

text{*We do not need to call things such as @{const transform_optimize_dnf_strict} because the
     firewall already is in @{const normalized_nnf_match} (required for @{const no_spoofing_iface})*}
lemma "transform_optimize_dnf_strict (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw)) =
          unfold_ruleset_INPUT action.Drop (map_of_string eduroam_fw)" by eval

text{* The ruleset prevents spoofed incoming packets *}
lemma "no_spoofing_iface (Iface ''wlan0'') ipassignment_incoming (unfold_ruleset_INPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw))" by eval


text{*Ruleset does not prevent that I'm spoofing (which is not necessary anyways since I need root right to spoof, which 
      would also enable me to deactivate the firewall). This is only a one-user laptop!*}

lemma "transform_optimize_dnf_strict (unfold_ruleset_OUTPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw)) =
        unfold_ruleset_OUTPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw)" by eval

lemma "\<not> no_spoofing_iface (Iface ''wlan0'') ipassignment_outgoing (unfold_ruleset_OUTPUT eduroam_fw_INPUT_default_policy (map_of_string eduroam_fw))" by eval


end
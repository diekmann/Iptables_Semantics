theory SNS_IAS_Eduroam_Spoofing
imports "../Code_Interface"
  "../../Primitive_Matchers/No_Spoof"
  test_Lnv
begin


section{*Example: Chair for Network Architectures and Services (TUM)*}


definition "everything_but_my_ip = ipv4range_split (ipv4range_invert (ipv4_cidr_tuple_to_interval (ipv4addr_of_dotdecimal (131,159,207,206), 32)))"


text{*This is really the range of everything but my ip*}
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


(* Incoming: everything but my ip *)
definition "ipassignment_incoming = ([Iface ''wlan0'' \<mapsto> everything_but_my_ip]:: ipassignment)"

(* Outgoing: only my IP*)
definition "ipassignment_outgoing = ([Iface ''wlan0'' \<mapsto> [(ipv4addr_of_dotdecimal (131,159,207,206), 32)]]:: ipassignment)"


(* ../../importer/main.py --import "../Code_Interface" test_Lnv test_Lnv.thy *)


value(code) "unfold_ruleset_INPUT action.Drop firewall_chains"

text{*Ruleset prevents spoofed incoming packets*}
value(code) "map simple_rule_toString (to_simple_firewall (upper_closure (unfold_ruleset_INPUT action.Drop firewall_chains)))"
lemma "transform_optimize_dnf_strict (unfold_ruleset_INPUT action.Drop firewall_chains) = unfold_ruleset_INPUT action.Drop firewall_chains" by eval
lemma "no_spoofing_iface (Iface ''wlan0'') ipassignment_incoming (unfold_ruleset_INPUT action.Drop firewall_chains)" by eval


text{*Ruleset does not prevent that I'm spoofing (which is not necessary anyways since I need root right to spoof, which 
      would also enable me to deactivate the firewall). This is only a one-user laptop!*}
value(code) "map simple_rule_toString (to_simple_firewall (upper_closure (unfold_ruleset_OUTPUT action.Drop firewall_chains)))"
lemma "transform_optimize_dnf_strict (unfold_ruleset_OUTPUT action.Drop firewall_chains) = unfold_ruleset_OUTPUT action.Drop firewall_chains" by eval
lemma "\<not> no_spoofing_iface (Iface ''wlan0'') ipassignment_outgoing (unfold_ruleset_OUTPUT action.Drop firewall_chains)" by eval


end
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


(* only my local interface *)
definition "example_ipassignment_nospoof = 
    no_spoofing_iface (Iface ''wlan0'') ([Iface ''wlan0'' \<mapsto> everything_but_my_ip]:: ipassignment)"


(* ../../importer/main.py --import "../Code_Interface" test_Lnv test_Lnv.thy *)


value(code) "unfold_ruleset_INPUT firewall_chains"

value(code) "map simple_rule_toString (to_simple_firewall (upper_closure (unfold_ruleset_INPUT firewall_chains)))"


lemma "transform_optimize_dnf_strict (unfold_ruleset_INPUT firewall_chains) = unfold_ruleset_INPUT firewall_chains" by eval

lemma "example_ipassignment_nospoof (unfold_ruleset_INPUT firewall_chains)" by eval


end
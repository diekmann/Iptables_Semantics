theory Analyze_medium_sized_company
imports 
  "../../Primitive_Matchers/Parser"
  "../../Semantics_Ternary/Optimizing"
  "../../Simple_Firewall/SimpleFw_toString"
begin



parse_iptables_save company_fw="iptables-save"

thm company_fw_def
thm company_fw_INPUT_default_policy_def

value[code] "map (\<lambda>(c,rs). (c, map (quote_rewrite \<circ> common_primitive_rule_toString) rs)) company_fw"

definition "unfolded_INPUT = unfold_ruleset_INPUT company_fw_INPUT_default_policy (map_of_string (company_fw))"

value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (unfolded_INPUT)"

value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (upper_closure unfolded_INPUT)"


value[code] "upper_closure (packet_assume_new unfolded_INPUT)"

lemma "check_simple_fw_preconditions (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded_INPUT))))" by eval


value[code] "map simple_rule_toString (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded_INPUT)))))"

value[code] "map simple_rule_toString (to_simple_firewall (lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded_INPUT)))))"









definition "unfolded_FORWARD = unfold_ruleset_FORWARD company_fw_FORWARD_default_policy (map_of_string (company_fw))"

value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (unfolded_FORWARD)"


value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (upper_closure unfolded_FORWARD)"


value[code] "upper_closure (packet_assume_new unfolded_FORWARD)"

lemma "check_simple_fw_preconditions (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded_FORWARD))))" by eval


value[code] "map simple_rule_toString (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded_FORWARD)))))"

value[code] "map simple_rule_toString (to_simple_firewall (lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded_FORWARD)))))"


(*
text{*If we call the IP address spcae partitioning incorrectly (not prepocessed, still has interfaces), we get an error*}
value[code] " parts_connection_ssh 
  (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded_FORWARD)))))"
*)


(*Interfaces be gone! necessary for ip partition!*)
definition preprocess where
  "preprocess unfold closure ipassmt def fw \<equiv> to_simple_firewall (closure
              (optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_L4_Flags a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_Prot a \<or> is_L4_Flags a))
              (closure
              (iface_try_rewrite ipassmt
              (closure
              (packet_assume_new
              (unfold def (map_of fw))))))))"

 definition "ipassmt = [(Iface ''lo'', [(ipv4addr_of_dotdecimal (127,0,0,0),8)]),
  (Iface ''eth0'', [(ipv4addr_of_dotdecimal (172,16,2,0),24)])
  ]"

value[code] "access_matrix_pretty parts_connection_ssh (preprocess unfold_ruleset_FORWARD upper_closure ipassmt company_fw_FORWARD_default_policy company_fw)"

value[code] "access_matrix_pretty parts_connection_http (preprocess unfold_ruleset_FORWARD upper_closure ipassmt company_fw_FORWARD_default_policy company_fw)"

end

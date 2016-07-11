theory Analyze_SQRL_Shorewall
imports 
  "../../Primitive_Matchers/Parser"
begin


section\<open>Example: SQRL Shorewall\<close>


parse_iptables_save SQRL_fw="iptables-saveakachan"


thm SQRL_fw_def
thm SQRL_fw_FORWARD_default_policy_def

value[code] "map (\<lambda>(c,rs). (c, map (quote_rewrite \<circ> common_primitive_rule_toString) rs)) SQRL_fw"

lemma "Semantics_Goto.terminal_chain (the ((map_of_string_ipv4 SQRL_fw) ''smurflog''))" by eval
lemma "Semantics_Goto.terminal_chain (the ((map_of_string_ipv4 SQRL_fw) ''logflags''))" by eval
lemma "Semantics_Goto.terminal_chain (the ((map_of_string_ipv4 SQRL_fw) ''reject''))" by eval

(*12.942s*)
value[code] "Semantics_Goto.rewrite_Goto SQRL_fw"

definition "unfolded = unfold_ruleset_FORWARD SQRL_fw_FORWARD_default_policy (map_of_string_ipv4 (Semantics_Goto.rewrite_Goto SQRL_fw))"

(*
(*2174.839s elapsed time, 3308.410s cpu time, 161.539s GC time*)
value[code] "unfolded"*)
(*0.561s*)
value[code] "let x = unfolded in ()" (*pretty printing is slow, not the unfolding! ML forces evaluation of unfolded!*)
(*39.149s*)
value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (unfolded)"
(*2.871s*)
lemma "length unfolded = 2649" by eval


(*17.554s*)
value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (upper_closure unfolded)"
lemma "length (upper_closure unfolded) = 1986" by eval


value[code] "upper_closure (packet_assume_new unfolded)"

(*28.550s*)
lemma "length (lower_closure unfolded) = 5715" by eval

lemma "check_simple_fw_preconditions (upper_closure unfolded) = False" by eval
lemma "\<forall>m \<in> get_match`set (upper_closure (packet_assume_new unfolded)). normalized_nnf_match m" by eval

lemma "\<forall>m \<in> get_match`set (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded))). normalized_nnf_match m" by eval

lemma "check_simple_fw_preconditions (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded))))" by eval
lemma "length (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded))))) = 1389" by eval
(*22.240s*)
value[code] "map simple_rule_ipv4_toString (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded)))))"

(*25.480s*)
value[code] "map ipv4addr_wordinterval_toString (getParts (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded))))))"

(*43.702s*)
lemma "length (to_simple_firewall (lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded))))) = 5120" by eval

(*71.518s*)
value[code] "length (remdups_rev (to_simple_firewall (lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded))))))" (*not smaller*)

value[code] "map ipv4addr_wordinterval_toString (getParts (to_simple_firewall (lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded))))))"

lemma "simple_fw_valid (to_simple_firewall (lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded)))))" by eval
lemma "simple_fw_valid (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded)))))" by eval

end

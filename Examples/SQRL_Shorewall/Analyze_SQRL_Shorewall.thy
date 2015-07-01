theory Analyze_SQRL_Shorewall
imports "../Code_Interface"
"../../Semantics_Ternary/Optimizing"
"../Parser"
"../../Semantics_Goto"
begin


section{*Example: SQRL Shorewall*}


parse_iptables_save SQRL_fw="iptables-saveakachan"


thm SQRL_fw_def
thm SQRL_fw_FORWARD_default_policy_def

value[code] "map (\<lambda>(c,rs). (c, map (quote_rewrite \<circ> common_primitive_rule_toString) rs)) SQRL_fw"

lemma "Semantics_Goto.terminal_chain (the ((map_of_string SQRL_fw) ''smurflog''))" by eval
lemma "Semantics_Goto.terminal_chain (the ((map_of_string SQRL_fw) ''logflags''))" by eval
lemma "Semantics_Goto.terminal_chain (the ((map_of_string SQRL_fw) ''reject''))" by eval

value[code] "Semantics_Goto.rewrite_Goto SQRL_fw"

definition "unfolded = unfold_ruleset_FORWARD SQRL_fw_FORWARD_default_policy (map_of_string (Semantics_Goto.rewrite_Goto SQRL_fw))"

(*31.053s*)
value[code] "unfolded"
(*2.871s*)
lemma "length unfolded = 2649" by eval

(*11.918s*)
value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (upper_closure unfolded)"
lemma "length (upper_closure unfolded) = 1430" by eval


(*53.507s*)
lemma "length (lower_closure unfolded) = 9574" by eval

(*16.334s*)
value[code] "map simple_rule_toString (to_simple_firewall (upper_closure unfolded))" 
lemma "length (to_simple_firewall (upper_closure unfolded)) = 1430" by eval

(*81.437s*)
lemma "length (to_simple_firewall (lower_closure unfolded)) = 6648" by eval

value[code] "length (remdups_rev (to_simple_firewall (lower_closure unfolded)))" (*even smaller*)


end

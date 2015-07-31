theory Analyze_SQRL_Shorewall
imports 
  "../../Primitive_Matchers/Parser"
  "../../Semantics_Ternary/Optimizing"
  "../../Simple_Firewall/SimpleFw_toString"
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

(*
(*2174.839s elapsed time, 3308.410s cpu time, 161.539s GC time*)
value[code] "unfolded"*)
(*0.561s*)
value[code] "let x = unfolded in ()" (*pretty printing is slow, not the unfolding! ML forces evaluation of unfolded!*)
(*39.257s*)
value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (unfolded)"
(*2.871s*)
lemma "length unfolded = 2649" by eval


(*19.119s*)
value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (upper_closure unfolded)"
lemma "length (upper_closure unfolded) = 1437" by eval


(*53.507s*)
value[code] "length (lower_closure unfolded)"
lemma "length (lower_closure unfolded) = 9642" by eval

lemma "check_simple_fw_preconditions (upper_closure unfolded) = False" by eval
lemma "check_simple_fw_preconditions (ctstate_assume_new (upper_closure unfolded))" by eval
lemma "length (to_simple_firewall (ctstate_assume_new (upper_closure unfolded))) = 1369" by eval
(*16.334s*)
value[code] "map simple_rule_toString (to_simple_firewall (ctstate_assume_new (upper_closure unfolded)))"

(*101.907s*)
lemma "length (to_simple_firewall (ctstate_assume_new (lower_closure unfolded))) = 6648" by eval

value[code] "length (remdups_rev (to_simple_firewall (ctstate_assume_new (lower_closure unfolded))))" (*even smaller*)


end

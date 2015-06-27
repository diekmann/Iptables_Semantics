theory Analyze_SQRL_Shorewall
imports "../Code_Interface"
"../../Semantics_Ternary/Optimizing"
"../Parser"
"../../Semantics_Goto"
begin


section{*Example: SQRL Shorewall*}


local_setup_parse_iptables_save SQRL_fw="iptables-saveakachan"


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


export_code unfold_ruleset_FORWARD map_of_string upper_closure lower_closure
  Rule
  Accept Drop Log Reject Call Return Empty  Unknown
  Match MatchNot MatchAnd MatchAny
  Ip4Addr Ip4AddrNetmask
  ProtoAny Proto TCP UDP
  Src Dst Prot Extra OIface IIface Src_Ports Dst_Ports
  Iface
  nat_of_integer
  check_simple_fw_preconditions
  to_simple_firewall
  simple_rule_toString
  Drop
  common_primitive_rule_toString
  in SML module_name "Test" file "unfold_code.ML"

ML_file "unfold_code.ML"

ML{*
open Test; (*put the exported code into current namespace such that the following firewall definition loads*)
*}

(*./main.py -t ml --module=Test  ../Examples/SQRL_Shorewall/akachan-iptables-Ln ../Examples/SQRL_Shorewall/akachan-iptables-Ln.ML
*)
(*TODO: this file has parsed gotos as calls!*)
ML_file "akachan-iptables-Ln.ML"

ML{*
open Test;
*}
declare[[ML_print_depth=50]]



ML{*
val rules = unfold_ruleset_FORWARD Drop (map_of_string firewall_chains)
*}

ML_val{*
map (common_primitive_rule_toString #> String.implode #> writeln) rules
*}

ML{*
length rules;
val upper = upper_closure rules;
val lower = lower_closure rules;
length upper;
length lower;*}


ML_val{*
map (common_primitive_rule_toString #> String.implode #> writeln) lower
*}

ML_val{*
check_simple_fw_preconditions upper;
check_simple_fw_preconditions lower;
*}

ML_val{*
length (to_simple_firewall upper);
length (to_simple_firewall lower);
*}


ML{*
val putLn = writeln o String.implode o simple_rule_toString;
*}


text{*iptables -L -n*}
ML_val{*
writeln "Chain INPUT (policy DROP)";
writeln "target     prot opt source               destination";
writeln "";
writeln "Chain FORWARD (policy DROP)";
writeln "target     prot opt source               destination";
val _ = map putLn (to_simple_firewall upper);
writeln "Chain OUTPUT (policy DROP)";
writeln "target     prot opt source               destination"
*}


text{*iptables -L -n*}
ML_val{*
writeln "Chain INPUT (policy DROP)";
writeln "target     prot opt source               destination";
writeln "";
writeln "Chain FORWARD (policy DROP)";
writeln "target     prot opt source               destination";
val _ = map putLn (to_simple_firewall lower);
writeln "Chain OUTPUT (policy DROP)";
writeln "target     prot opt source               destination"
*}
end

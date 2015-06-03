theory Analyze_SQRL_Shorewall
imports "../Code_Interface"
"../../Semantics_Ternary/Optimizing"
begin


section{*Example: SQRL Shorewall*}

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

theory Analyze_TUM_Net_Firewall_new
imports Main "../../Primitive_Matchers/Transform" "../../Call_Return_Unfolding" "../../Simple_Firewall/SimpleFw_Compliance"
"~~/src/HOL/Library/Code_Target_Nat"
"~~/src/HOL/Library/Code_Target_Int"
"~~/src/HOL/Library/Code_Char"
begin


section{*Example: Chair for Network Architectures and Services (TUM)*}

definition unfold_ruleset_FORWARD :: "common_primitive ruleset \<Rightarrow> common_primitive rule list" where
"unfold_ruleset_FORWARD rs = ((optimize_matches opt_MatchAny_match_expr)^^10) 
  (optimize_matches optimize_primitive_univ (rw_Reject (rm_LogEmpty (((process_call rs)^^5) [Rule MatchAny (Call ''FORWARD'')]))))"


definition map_of_string :: "(string \<times> common_primitive rule list) list \<Rightarrow> string \<rightharpoonup> common_primitive rule list" where
"map_of_string rs = map_of rs"


definition upper_closure :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "upper_closure rs == transform_optimize_dnf_strict (transform_normalize_primitives (transform_optimize_dnf_strict (optimize_matches_a upper_closure_matchexpr rs)))"
(*definition lower_closure :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "lower_closure rs == rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^2000) (optimize_matches_a lower_closure_matchexpr rs))"*)


export_code unfold_ruleset_FORWARD map_of_string upper_closure  
  Rule
  Accept Drop Log Reject Call Return Empty  Unknown
  Match MatchNot MatchAnd MatchAny
  Ip4Addr Ip4AddrNetmask
  ProtoAny Proto TCP UDP
  Src Dst Prot Extra OIface IIface
  Iface
  nat_of_integer integer_of_nat
  dotdecimal_of_ipv4addr
  check_simple_fw_preconditions
  to_simple_firewall
  SimpleRule simple_action.Accept simple_action.Drop 
  iiface oiface src dst proto sports dports
  in SML module_name "Test" file "unfold_code.ML"

ML_file "unfold_code.ML"

(*we search replaced brute-forcely to adapt to the new constructor names
*)
ML_file "iptables_Ln_29.11.2013_new_deletemeaftertesting.ML"

ML{*
open Test;
*}
declare[[ML_print_depth=50]]
ML{*
val rules = unfold_ruleset_FORWARD (map_of_string firewall_chains)
*}
ML{*
length rules;
val upper = upper_closure rules;
length upper;*}

text{*How long does the unfolding take?*}
ML_val{*
val t0 = Time.now();
val _ = unfold_ruleset_FORWARD (map_of_string firewall_chains);
val t1= Time.now();
writeln(String.concat ["It took ", Time.toString(Time.-(t1,t0)), " seconds"])
*}
text{*on my system, less than 1 second.*}

text{*Time required for calculating and normalizing closure*}
ML_val{*
val t0 = Time.now();
val _ = upper_closure rules;
val t1= Time.now();
writeln(String.concat ["It took ", Time.toString(Time.-(t1,t0)), " seconds"])
*}
text{*on my system, less than 20 seconds.*}


ML_val{*
check_simple_fw_preconditions upper
*}

ML_val{*
length (to_simple_firewall upper);
to_simple_firewall upper
*}


ML{*
fun dump_dotdecimal_ip (a,(b,(c,d))) = ""^ Int.toString (integer_of_nat a)^"."^ Int.toString (integer_of_nat b)^"."^ Int.toString (integer_of_nat c)^"."^ Int.toString (integer_of_nat d);

fun dump_ip (base, n) = (dump_dotdecimal_ip (dotdecimal_of_ipv4addr base))^"/"^ Int.toString (integer_of_nat n);

fun dump_prot ProtoAny = "all"
  | dump_prot (Proto TCP) = "tcp"
  | dump_prot (Proto UDP) = "udp";


fun dump_action (Accepta : simple_action) = "ACCEPT"
  | dump_action (Dropa   : simple_action) = "DROP";

fun dump_iface_name (descr: string) (Iface name) = (let val iface=String.implode name in (if iface = "" orelse iface = "+" then "" else descr^" "^iface) end)


fun dump_iptables [] = ()
  | dump_iptables (SimpleRule (m, a) :: rs) =
      (writeln (dump_action a ^ "     " ^
               (dump_prot (proto m)) ^ "  --  " ^
               (dump_ip (src m)) ^ "            " ^
               (dump_ip (dst m)) ^ "     " ^
               (dump_iface_name "in:" (iiface m)) ^ " " ^
               (dump_iface_name "out:" (oiface m)) ^ " " ^
                "also dump here: sports dports"); dump_iptables rs);

*}

ML_val{*
dump_iptables (to_simple_firewall upper);
*}

text{*iptables -L -n*}

ML_val{*
writeln "Chain INPUT (policy ACCEPT)";
writeln "target     prot opt source               destination";
writeln "";
writeln "Chain FORWARD (policy ACCEPT)";
writeln "target     prot opt source               destination";
dump_iptables (to_simple_firewall upper);
writeln "Chain OUTPUT (policy ACCEPT)";
writeln "target     prot opt source               destination"
*}

ML_val{*true*}


end

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
  Src Dst Prot Extra
  nat_of_integer integer_of_nat
  Pos Neg
  check_simple_fw_preconditions
  to_simple_firewall
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
(take 1 upper)
*}

(*fails, ...*)
ML_val{*
to_simple_firewall upper
*}

ML_val{*true*}


end

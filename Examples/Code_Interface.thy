theory Code_Interface
imports Main "../Primitive_Matchers/Transform" "../Call_Return_Unfolding" "../Simple_Firewall/SimpleFw_Compliance"
"~~/src/HOL/Library/Code_Target_Nat"
"~~/src/HOL/Library/Code_Target_Int"
"~~/src/HOL/Library/Code_Char"
begin


section{*Code Interface*}

definition unfold_ruleset_FORWARD :: "common_primitive ruleset \<Rightarrow> common_primitive rule list" where
"unfold_ruleset_FORWARD rs = ((optimize_matches opt_MatchAny_match_expr)^^10) 
  (optimize_matches optimize_primitive_univ (rw_Reject (rm_LogEmpty (((process_call rs)^^5) [Rule MatchAny (Call ''FORWARD'')]))))"

definition map_of_string :: "(string \<times> common_primitive rule list) list \<Rightarrow> string \<rightharpoonup> common_primitive rule list" where
"map_of_string rs = map_of rs"

definition upper_closure :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "upper_closure rs == transform_optimize_dnf_strict (transform_normalize_primitives (transform_optimize_dnf_strict (optimize_matches_a upper_closure_matchexpr rs)))"
definition lower_closure :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "lower_closure rs == transform_optimize_dnf_strict (transform_normalize_primitives (transform_optimize_dnf_strict (optimize_matches_a lower_closure_matchexpr rs)))"

definition port_to_nat :: "16 word \<Rightarrow> nat" where
  "port_to_nat p = unat p"




definition bitmask_to_strange_inverse_cisco_mask:: "nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)" where
 "bitmask_to_strange_inverse_cisco_mask n \<equiv> dotdecimal_of_ipv4addr ( (NOT (((mask n)::ipv4addr) << (32 - n))) )"
lemma "bitmask_to_strange_inverse_cisco_mask 16 = (0, 0, 255, 255)" by eval
lemma "bitmask_to_strange_inverse_cisco_mask 24 = (0, 0, 0, 255)" by eval
lemma "bitmask_to_strange_inverse_cisco_mask 8 = (0, 255, 255, 255)" by eval
lemma "bitmask_to_strange_inverse_cisco_mask 32 = (0, 0, 0, 0)" by eval

end

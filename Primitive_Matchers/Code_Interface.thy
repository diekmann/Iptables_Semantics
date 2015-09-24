theory Code_Interface
imports 
  Common_Primitive_toString
  "../Call_Return_Unfolding"
  Transform
  Primitive_Abstract
  No_Spoof
  "../Simple_Firewall/SimpleFw_Compliance"
  "../Semantics_Goto"
  "~~/src/HOL/Library/Code_Target_Nat"
  "~~/src/HOL/Library/Code_Target_Int"
  "~~/src/HOL/Library/Code_Char"
begin


section{*Code Interface*}


text{*The parser returns the @{typ "common_primitive ruleset"} not as a map but as an association list.
      This function converts it*}
definition map_of_string :: "(string \<times> common_primitive rule list) list \<Rightarrow> string \<rightharpoonup> common_primitive rule list" where
  "map_of_string rs = map_of rs"


(*
text{*Remove an ESTABLISHED RELATED rule if it occurs in the first @{term "n::nat"} rules*}
fun remove_ESTABLISHED_RELATED_chain :: "nat \<Rightarrow> common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "remove_ESTABLISHED_RELATED_chain _ [] = []" |
  "remove_ESTABLISHED_RELATED_chain 0 rs = rs" |
  "remove_ESTABLISHED_RELATED_chain (Suc n) ((Rule m a)#rs) = (
    if opt_MatchAny_match_expr (optimize_primitive_univ m) = (Match (Extra (''state RELATED,ESTABLISHED''))) \<and> a = action.Accept
    then rs
    else (Rule m a)#remove_ESTABLISHED_RELATED_chain n rs)"

lemma "length (remove_ESTABLISHED_RELATED_chain n rs) = length rs \<or>
       length (remove_ESTABLISHED_RELATED_chain n rs) = length rs - 1"
  apply(induction n rs rule: remove_ESTABLISHED_RELATED_chain.induct)
    apply(simp_all)
  by linarith

text{*Remove RELATED,ESTABLISHED rules from the built-in chains if the rule is in the first five rules*}
definition remove_ESTABLISHED_RELATED :: "(string \<times> common_primitive rule list) list \<Rightarrow> (string \<times> common_primitive rule list) list" where
  "remove_ESTABLISHED_RELATED fw = map (\<lambda> (decl, rs).
    if decl \<in> {''INPUT'', ''FORWARD'', ''OUTPUT''} then (decl, remove_ESTABLISHED_RELATED_chain 5 rs)
    else (decl, rs)) fw"
*)


definition check_simple_ruleset :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "check_simple_ruleset rs \<equiv> if simple_ruleset rs then rs else undefined"

text{*repeat the application at most n times (param 1) until it stabilize*}
fun repeat_stabilize :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "repeat_stabilize 0 _ v = v" |
  "repeat_stabilize (Suc n) f v = (let v_new = f v in if v = v_new then v else repeat_stabilize n f v_new)"

lemma "repeat_stabilize n f v = (f^^n) v"
  proof(induction n arbitrary: v)
  case (Suc n)
    have "f v = v \<Longrightarrow> (f^^n) v = v" by(induction n) simp_all
    with Suc show ?case by(simp add: Let_def funpow_swap1)
  qed(simp)

(*TODO replace constant number of process_call with number of chain decls *)

definition unfold_ruleset_CHAIN :: "string \<Rightarrow> action \<Rightarrow> common_primitive ruleset \<Rightarrow> common_primitive rule list" where
"unfold_ruleset_CHAIN chain_name default_action rs = check_simple_ruleset
  (repeat_stabilize 1000 (optimize_matches opt_MatchAny_match_expr)
    (optimize_matches optimize_primitive_univ
      (rw_Reject (rm_LogEmpty (repeat_stabilize 10000 (process_call rs)
        [Rule MatchAny (Call chain_name), Rule MatchAny default_action]
  )))))"


definition unfold_ruleset_FORWARD :: "action \<Rightarrow> common_primitive ruleset \<Rightarrow> common_primitive rule list" where
"unfold_ruleset_FORWARD = unfold_ruleset_CHAIN ''FORWARD''"


definition unfold_ruleset_INPUT :: "action \<Rightarrow> common_primitive ruleset \<Rightarrow> common_primitive rule list" where
"unfold_ruleset_INPUT = unfold_ruleset_CHAIN ''INPUT''"

definition unfold_ruleset_OUTPUT :: "action \<Rightarrow> common_primitive ruleset \<Rightarrow> common_primitive rule list" where
"unfold_ruleset_OUTPUT \<equiv> unfold_ruleset_CHAIN ''OUTPUT''"




definition upper_closure :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "upper_closure rs == remdups_rev (transform_optimize_dnf_strict
      (transform_normalize_primitives (transform_optimize_dnf_strict (optimize_matches_a upper_closure_matchexpr rs))))"
definition lower_closure :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "lower_closure rs == remdups_rev (transform_optimize_dnf_strict
      (transform_normalize_primitives (transform_optimize_dnf_strict (optimize_matches_a lower_closure_matchexpr rs))))"


lemma "simple_ruleset rs \<Longrightarrow> check_simple_fw_preconditions (upper_closure (ctstate_assume_new rs))"
  apply(simp add: check_simple_fw_preconditions_def)
  apply(clarify)
  apply(rename_tac r, case_tac r, rename_tac m a)
  apply(simp)
  apply(drule ctstate_assume_new_simple_ruleset)
  unfolding upper_closure_def
  apply(simp add: remdups_rev_set)
  apply(frule transform_remove_unknowns_upper(4))
  apply(drule transform_remove_unknowns_upper(2))
  thm transform_optimize_dnf_strict[OF _ wf_in_doubt_allow]
  apply(frule(1) transform_optimize_dnf_strict(3)[OF _ wf_in_doubt_allow, where disc=is_Extra])
  apply(thin_tac "\<forall>m\<in>get_match ` set (optimize_matches_a upper_closure_matchexpr (ctstate_assume_new rs)). \<not> has_disc is_Extra m")
  apply(frule transform_optimize_dnf_strict(4)[OF _ wf_in_doubt_allow])
  apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_allow])
  thm transform_normalize_primitives[OF _ wf_in_doubt_allow]
  apply(frule(1) transform_normalize_primitives(3)[OF _ wf_in_doubt_allow, of _ is_Extra])
      apply(simp_all)[5]
  apply(thin_tac "\<forall>m\<in>get_match ` set (transform_optimize_dnf_strict (optimize_matches_a upper_closure_matchexpr (ctstate_assume_new rs))). \<not> has_disc is_Extra m")
  apply(frule(1) transform_normalize_primitives(5)[OF _ wf_in_doubt_allow])
  apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_allow], simp)

  apply(frule(1) transform_optimize_dnf_strict(3)[OF _ wf_in_doubt_allow, where disc=is_Extra])
  apply(frule transform_optimize_dnf_strict(4)[OF _ wf_in_doubt_allow])
  apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_allow])
  apply(subgoal_tac "(a = action.Accept \<or> a = action.Drop)")
   prefer 2
   apply(simp_all add: simple_ruleset_def)
   apply fastforce
  oops

(*
definition port_to_nat :: "16 word \<Rightarrow> nat" where
  "port_to_nat p = unat p"
*)

(* only used for ML code to convert types *)
definition nat_to_16word :: "nat \<Rightarrow> 16 word" where
  "nat_to_16word i \<equiv> of_nat i"

definition integer_to_16word :: "integer \<Rightarrow> 16 word" where
  "integer_to_16word i \<equiv> nat_to_16word (nat_of_integer i)"




definition bitmask_to_strange_inverse_cisco_mask:: "nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)" where
 "bitmask_to_strange_inverse_cisco_mask n \<equiv> dotdecimal_of_ipv4addr ( (NOT (((mask n)::ipv4addr) << (32 - n))) )"
lemma "bitmask_to_strange_inverse_cisco_mask 16 = (0, 0, 255, 255)" by eval
lemma "bitmask_to_strange_inverse_cisco_mask 24 = (0, 0, 0, 255)" by eval
lemma "bitmask_to_strange_inverse_cisco_mask 8 = (0, 255, 255, 255)" by eval
lemma "bitmask_to_strange_inverse_cisco_mask 32 = (0, 0, 0, 0)" by eval



end

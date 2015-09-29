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

(*Note: common_primitive_match_expr_toString can be really slow*)

section{*Code Interface*}


text{*The parser returns the @{typ "common_primitive ruleset"} not as a map but as an association list.
      This function converts it*}
definition map_of_string :: "(string \<times> common_primitive rule list) list \<Rightarrow> string \<rightharpoonup> common_primitive rule list" where
  "map_of_string rs = map_of rs"


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


text{*putting it all together*}
lemma transform_upper_closure:
  assumes simplers: "simple_ruleset rs"
  -- "semantics are preserved"
  shows "(common_matcher, in_doubt_allow),p\<turnstile> \<langle>upper_closure rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
  and "simple_ruleset (upper_closure rs)"
  -- "simple, normalized rules without unknowns"
  and "\<forall> m \<in> get_match ` set (upper_closure rs). normalized_nnf_match m \<and>
         normalized_src_ports m \<and>
         normalized_dst_ports m \<and>
         normalized_src_ips m \<and>
         normalized_dst_ips m \<and>
         \<not> has_disc is_Extra m"
  -- "no new primitives are introduced"
  and "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow>
        \<forall> r \<in> get_match ` set rs. \<not> has_disc disc r \<Longrightarrow> \<forall> r \<in> get_match ` set (upper_closure rs). \<not> has_disc disc r"
  and "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow>
        \<forall> r \<in> get_match ` set rs. \<not> has_disc_negated disc neg r \<Longrightarrow> \<forall> r \<in> get_match ` set (upper_closure rs). \<not> has_disc_negated disc neg r"
  proof -
    { fix m a
        have "Rule m a \<in> set (upper_closure rs) \<Longrightarrow>
            (a = action.Accept \<or> a = action.Drop) \<and>
             normalized_nnf_match m \<and>
             normalized_src_ports m \<and>
             normalized_dst_ports m \<and>
             normalized_src_ips m \<and>
             normalized_dst_ips m \<and>
              \<not> has_disc is_Extra m"
        using simplers
        unfolding upper_closure_def
        apply(simp add: remdups_rev_set)
        apply(frule transform_remove_unknowns_upper(4))
        apply(drule transform_remove_unknowns_upper(2))
        thm transform_optimize_dnf_strict[OF _ wf_in_doubt_allow]
        apply(frule(1) transform_optimize_dnf_strict(3)[OF _ wf_in_doubt_allow, where disc=is_Extra])
        apply(thin_tac "\<forall>m\<in>get_match ` set (optimize_matches_a upper_closure_matchexpr rs). \<not> has_disc is_Extra m")
        apply(frule transform_optimize_dnf_strict(4)[OF _ wf_in_doubt_allow])
        apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_allow])
        thm transform_normalize_primitives[OF _ wf_in_doubt_allow]
        apply(frule(1) transform_normalize_primitives(3)[OF _ wf_in_doubt_allow, of _ is_Extra])
          apply(simp_all)[2]
        apply(thin_tac "\<forall>m\<in>get_match ` set (transform_optimize_dnf_strict (optimize_matches_a upper_closure_matchexpr rs)). \<not> has_disc is_Extra m")
        apply(frule(1) transform_normalize_primitives(5)[OF _ wf_in_doubt_allow])
        apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_allow], simp)
        thm transform_optimize_dnf_strict[OF _ wf_in_doubt_allow]
        apply(frule(1) transform_optimize_dnf_strict(3)[OF _ wf_in_doubt_allow, where disc=is_Extra])
        apply(frule transform_optimize_dnf_strict(4)[OF _ wf_in_doubt_allow])
        apply(frule transform_optimize_dnf_strict(5)[OF _ wf_in_doubt_allow, of _ "(is_Src_Ports, src_ports_sel)" "(\<lambda>pts. length pts \<le> 1)"])
         apply(simp add: normalized_src_ports_def2; fail)
        apply(frule transform_optimize_dnf_strict(5)[OF _ wf_in_doubt_allow, of _ "(is_Dst_Ports, dst_ports_sel)" "(\<lambda>pts. length pts \<le> 1)"])
         apply(simp add: normalized_dst_ports_def2; fail)
        apply(frule transform_optimize_dnf_strict(5)[OF _ wf_in_doubt_allow, of _ "(is_Src, src_sel)" normalized_cidr_ip])
         apply(simp add: normalized_src_ips_def2; fail)
        apply(frule transform_optimize_dnf_strict(5)[OF _ wf_in_doubt_allow, of _ "(is_Dst, dst_sel)" normalized_cidr_ip])
         apply(simp add: normalized_dst_ips_def2; fail)
        apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_allow])
        apply(simp)
        apply(subgoal_tac "(a = action.Accept \<or> a = action.Drop)")
         prefer 2
         apply(simp_all add: simple_ruleset_def)
         apply fastforce
        apply(simp add: normalized_src_ports_def2 normalized_dst_ports_def2 normalized_src_ips_def2 normalized_dst_ips_def2)
        apply(intro conjI)
              apply fastforce+
        done
    } note 1=this

    from 1 show "simple_ruleset (upper_closure rs)"
      apply(simp add: simple_ruleset_def)
      apply(clarify)
      apply(rename_tac r)
      apply(case_tac r)
      apply(simp)
      by blast


    from 1 show "\<forall> m \<in> get_match ` set (upper_closure rs). normalized_nnf_match m \<and>
         normalized_src_ports m \<and>
         normalized_dst_ports m \<and>
         normalized_src_ips m \<and>
         normalized_dst_ips m \<and>
         \<not> has_disc is_Extra m"
      apply(simp)
      apply(clarify)
      apply(rename_tac r)
      apply(case_tac r)
      apply(simp)
      done
      

    show "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow>
            \<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow> \<forall> m \<in> get_match ` set (upper_closure rs). \<not> has_disc disc m"
    using simplers
    unfolding upper_closure_def
    apply - 
    apply(frule(1) transform_remove_unknowns_upper(3)[where disc=disc])
    apply(drule transform_remove_unknowns_upper(2))
    apply(frule(1) transform_optimize_dnf_strict(3)[OF _ wf_in_doubt_allow, where disc=disc])
    apply(frule transform_optimize_dnf_strict(4)[OF _ wf_in_doubt_allow])
    apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_allow])
    apply(frule(1) transform_normalize_primitives(3)[OF _ wf_in_doubt_allow, of _ disc])
      apply(simp_all)[2]
    apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_allow], simp)
    apply(frule(1) transform_optimize_dnf_strict(3)[OF _ wf_in_doubt_allow, where disc=disc])
    apply(simp add: remdups_rev_set)
    done

    show"\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow>
        \<forall> r \<in> get_match ` set rs. \<not> has_disc_negated disc neg r \<Longrightarrow> \<forall> r \<in> get_match ` set (upper_closure rs). \<not> has_disc_negated disc neg r"
    using simplers
    unfolding upper_closure_def
    apply - 
    apply(frule(1) transform_remove_unknowns_upper(6)[where disc=disc])
    apply(drule transform_remove_unknowns_upper(2))
    apply(frule(1) transform_optimize_dnf_strict(6)[OF _ wf_in_doubt_allow, where disc=disc])
    apply(frule transform_optimize_dnf_strict(4)[OF _ wf_in_doubt_allow])
    apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_allow])
    apply(frule(1) transform_normalize_primitives(7)[OF _ wf_in_doubt_allow, of _ disc])
      apply(simp_all)[2]
    apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_allow], simp)
    apply(frule(1) transform_optimize_dnf_strict(6)[OF _ wf_in_doubt_allow, where disc=disc])
    apply(simp add: remdups_rev_set)
    done

    show "(common_matcher, in_doubt_allow),p\<turnstile> \<langle>upper_closure rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
    using simplers
    unfolding upper_closure_def
    apply -
    apply(frule transform_remove_unknowns_upper(1)[where p=p and s=s and t=t])
    apply(drule transform_remove_unknowns_upper(2))
    apply(frule transform_optimize_dnf_strict(1)[OF _ wf_in_doubt_allow, where p=p and s=s and t=t])
    apply(frule transform_optimize_dnf_strict(4)[OF _ wf_in_doubt_allow])
    apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_allow])
    apply(frule(1) transform_normalize_primitives(1)[OF _ wf_in_doubt_allow, where p=p and s=s and t=t])
    apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_allow], simp)
    apply(frule transform_optimize_dnf_strict(1)[OF _ wf_in_doubt_allow, where p=p and s=s and t=t])
    apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_allow])
    apply(simp)
    using approximating_bigstep_fun_remdups_rev
    by (simp add: approximating_bigstep_fun_remdups_rev approximating_semantics_iff_fun_good_ruleset remdups_rev_simplers simple_imp_good_ruleset) 
  qed

  
lemma ctstate_assume_new_not_has_CT_State:
  "m \<in> get_match ` set (ctstate_assume_new rs) \<Longrightarrow> \<not> has_disc is_CT_State m"
  apply(simp add: ctstate_assume_new_def)
  apply(induction rs)
   apply(simp add: optimize_matches_def; fail)
  apply(simp add: optimize_matches_def)
  apply(safe)
   apply(simp_all add: not_hasdisc_ctstate_assume_state)
  done

lemma transform_simple_fw_preconditions:
  assumes simplers: "simple_ruleset rs"
  shows "check_simple_fw_preconditions (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new rs))))"
  unfolding check_simple_fw_preconditions_def
  apply(clarify, rename_tac r, case_tac r, rename_tac m a, simp)
  proof -
    let ?rs3="optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new rs))"
    let ?rs'="upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new rs)))"
    fix m a
    assume r: "Rule m a \<in> set ?rs'"
    from packet_assume_new_simple_ruleset[OF simplers] have s1: "simple_ruleset (packet_assume_new rs)" .
    from transform_upper_closure(2)[OF s1] have s2: "simple_ruleset (upper_closure (packet_assume_new rs))" .
    from s2 have s3: "simple_ruleset ?rs3" by (simp add: optimize_matches_simple_ruleset) 
    from transform_upper_closure(2)[OF s3] have s4: "simple_ruleset ?rs'" .
    with r have a: "(a = action.Accept \<or> a = action.Drop)" by(auto simp add: simple_ruleset_def)
      
    
    have "\<And>m. m \<in> get_match ` set (packet_assume_new rs) \<Longrightarrow> \<not> has_disc is_CT_State m"
      by(simp add: packet_assume_new_def ctstate_assume_new_not_has_CT_State)
    with transform_upper_closure(4)[OF s1, where disc=is_CT_State] have
      "\<forall>m\<in>get_match ` set (upper_closure (packet_assume_new rs)). \<not> has_disc is_CT_State m"
      by fastforce
    with abstract_primitive_preserves_nodisc[where disc'="is_CT_State"] have "\<forall>m\<in>get_match ` set ?rs3. \<not> has_disc is_CT_State m"
      apply -
      apply(rule optimize_matches_preserves)
      apply(simp add: abstract_for_simple_firewall_def)
      done
    with transform_upper_closure(4)[OF s3, where disc=is_CT_State] have "\<forall>m\<in>get_match ` set ?rs'. \<not> has_disc is_CT_State m" by fastforce
    with r have no_CT: "\<not> has_disc is_CT_State m" by fastforce

    from abstract_for_simple_firewall_hasdisc have "\<forall>m\<in>get_match ` set ?rs3. \<not> has_disc is_L4_Flags m"
      apply -
      apply(rule optimize_matches_preserves, simp)
      done
    with transform_upper_closure(4)[OF s3, where disc=is_L4_Flags] have "\<forall>m\<in>get_match ` set ?rs'. \<not> has_disc is_L4_Flags m" by fastforce
    with r have no_L4_Flags: "\<not> has_disc is_L4_Flags m" by fastforce

    from transform_upper_closure(3)[OF s1] have "\<forall>m\<in>get_match ` set (upper_closure (packet_assume_new rs)). normalized_nnf_match m" by simp
    with abstract_for_simple_firewall_negated_ifaces_prots have
      ifaces: "\<forall>m\<in>get_match ` set ?rs3. \<not> has_disc_negated (\<lambda>a. is_Iiface a \<or> is_Oiface a) False m" and
      protocols: "\<forall>m\<in>get_match ` set ?rs3. \<not> has_disc_negated is_Prot False m" 
      apply -
      apply(rule optimize_matches_preserves, simp)+
      done

    from transform_upper_closure(3)[OF s3] have "\<forall>m\<in>get_match ` set ?rs'.
     normalized_nnf_match m \<and> normalized_src_ports m \<and> normalized_dst_ports m \<and> normalized_src_ips m \<and> normalized_dst_ips m \<and> \<not> has_disc is_Extra m" .
    with r have normalized: "normalized_src_ports m \<and> normalized_dst_ports m \<and> normalized_src_ips m \<and> normalized_dst_ips m \<and> \<not> has_disc is_Extra m" by fastforce


    from transform_upper_closure(5)[OF s3] ifaces protocols have "\<forall>m\<in>get_match ` set ?rs'.
     \<not> has_disc_negated (\<lambda>a. is_Iiface a \<or> is_Oiface a) False m \<and> \<not> has_disc_negated is_Prot False m" by simp (*500ms*)
    with r have abstracted: "normalized_ifaces m \<and> normalized_protocols m"
    unfolding normalized_protocols_def normalized_ifaces_def by fastforce
    
    from no_CT no_L4_Flags s4 normalized a abstracted show "normalized_src_ports m \<and>
             normalized_dst_ports m \<and>
             normalized_src_ips m \<and>
             normalized_dst_ips m \<and>
             normalized_ifaces m \<and>
             normalized_protocols m \<and> \<not> has_disc is_L4_Flags m \<and> \<not> has_disc is_CT_State m \<and> \<not> has_disc is_Extra m \<and> (a = action.Accept \<or> a = action.Drop)"
      by(simp)
  qed



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

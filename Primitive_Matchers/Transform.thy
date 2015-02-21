theory Transform
imports "Common_Primitive_Matcher"
        "../Semantics_Ternary"
        "../Output_Format/Negation_Type_Matching"
        "../Primitive_Matchers/Ports_Normalize"
        "../Primitive_Matchers/IpAddresses_Normalize"
begin

definition transform_strict :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where 
    "transform_strict = optimize_matches opt_MatchAny_match_expr(*^^10)*) \<circ> normalize_rules \<circ> optimize_matches optimize_primitive_univ \<circ> rw_Reject \<circ> rm_LogEmpty"


lemma assumes goodrs: "good_ruleset rs" and wf\<alpha>: "wf_unknown_match_tac \<alpha>"
      shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>transform_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      and "simple_ruleset (transform_strict rs)"
      and "\<forall> r \<in> set (transform_strict rs). normalized_match (get_match r)"
  proof -
    let ?\<gamma>="(common_matcher, \<alpha>)"
    let ?fw="\<lambda>rs. approximating_bigstep_fun ?\<gamma> p rs s"
    from approximating_semantics_iff_fun_good_ruleset goodrs have 1: "?\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> ?fw rs = t" by fast

    let ?rs2="(rw_Reject (rm_LogEmpty rs))"
    from goodrs rmLogEmpty_rwReject_good_to_simple have simple_rs2: "simple_ruleset ?rs2" by blast

    let ?rs3="(optimize_matches optimize_primitive_univ ?rs2)"
    from simple_rs2 optimize_matches_simple_ruleset have simple_rs3: "simple_ruleset ?rs3" by auto

    let ?rs4="(normalize_rules ?rs3)"
    from simple_rs3 simple_ruleset_normalize_rules have simple_rs4: "simple_ruleset ?rs4" by auto
    {fix rs::"'a rule list"
      have "\<forall> r \<in> set (normalize_rules rs). normalized_match (get_match r)"
        apply(induction rs)
         apply(simp)
        apply(rename_tac r rs, case_tac r)
        using normalized_match_normalize_match by fastforce
      } hence normalized_rs4: "\<forall> r \<in> set (normalize_rules ?rs4). normalized_match (get_match r)" by auto

    let ?rs5="optimize_matches opt_MatchAny_match_expr ?rs4"
    from simple_rs4 optimize_matches_simple_ruleset have simple_rs5: "simple_ruleset ?rs5" by auto

    from approximating_semantics_iff_fun_good_ruleset simple_rs5 simple_imp_good_ruleset have 2: 
      "?fw ?rs5 = t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>transform_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      unfolding transform_strict_def by fastforce

    have "?fw rs = ?fw (rm_LogEmpty rs)" using rm_LogEmpty_fun_semantics[symmetric] by fast
    also have "\<dots> = ?fw ?rs2" using rw_Reject_fun_semantics wf\<alpha> by metis
    also have "\<dots> = ?fw ?rs3"
      apply(rule optimize_matches[symmetric])
      using optimize_primitive_univ_correct_matchexpr by force
    also have "\<dots> = ?fw ?rs4"
      apply(rule normalize_rules_correct[symmetric])
      using simple_rs3 by (metis good_imp_wf_ruleset simple_imp_good_ruleset)
    also have "\<dots> = ?fw ?rs5" by (metis optimize_matches_opt_MatchAny_match_expr) 
    finally have rs: "?fw rs = ?fw ?rs5" .
    
    from 1 2 rs show  "(common_matcher, \<alpha>),p\<turnstile> \<langle>transform_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t" by presburger

    from simple_rs5 show "simple_ruleset (transform_strict rs)"
      by(simp add: transform_strict_def)

    show "\<forall> r \<in> set (transform_strict rs). normalized_match (get_match r)"  oops
  (*qed*)

end

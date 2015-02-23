theory Transform
imports "Common_Primitive_Matcher"
        "../Semantics_Ternary"
        "../Output_Format/Negation_Type_Matching"
        "../Primitive_Matchers/Ports_Normalize"
        "../Primitive_Matchers/IpAddresses_Normalize"
begin

(*closure bounds*)

(*def: transform_optimize = optimize_matches opt_MatchAny_match_expr \<circ> optimize_matches optimize_primitive_univ
apply before and after nralizatin and closures
*)

(*this cannot be normalized as it can contain MatchNot MatchAny*)
definition transform_optimize_strict :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where 
    "transform_optimize_strict = optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ)"

theorem transform_optimize_strict: assumes simplers: "simple_ruleset rs" and wf\<alpha>: "wf_unknown_match_tac \<alpha>"
      shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>transform_optimize_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      and "simple_ruleset (transform_optimize_strict rs)"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc C m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_strict rs). \<not> has_disc C m"
      and "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_strict rs). normalized_nnf_match m"
      and "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_strict rs). normalized_n_primitive disc_sel f m"
  proof -
    let ?\<gamma>="(common_matcher, \<alpha>)"
    let ?fw="\<lambda>rs. approximating_bigstep_fun ?\<gamma> p rs s"

    show simplers_transform: "simple_ruleset (transform_optimize_strict rs)"
      unfolding transform_optimize_strict_def
      using simplers optimize_matches_simple_ruleset by fast

    have 1: "?\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> ?fw rs = t"
      using approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers]] by fast
    have rs: "?fw rs = ?fw (transform_optimize_strict rs)"
      unfolding transform_optimize_strict_def
      apply(rule optimize_matches[symmetric])
      using optimize_primitive_univ_correct_matchexpr opt_MatchAny_match_expr_correct by (metis comp_apply)
    have 2: "?fw (transform_optimize_strict rs) = t \<longleftrightarrow> ?\<gamma>,p\<turnstile> \<langle>transform_optimize_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t "
      using approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers_transform], symmetric] by fast
    from 1 2 rs show "?\<gamma>,p\<turnstile> \<langle>transform_optimize_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> ?\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t" by simp

    { fix P m
      assume p1: "\<forall>m. P m \<longrightarrow> P (optimize_primitive_univ m)"
      assume p2: "\<forall>m. P m \<longrightarrow> P (opt_MatchAny_match_expr m)"
      from p1 p2 have "\<forall> m \<in> get_match ` set rs. P m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_strict rs). P m"
        unfolding transform_optimize_strict_def optimize_matches_def
        by(induction rs) (simp_all)
    } note matchpred_rule=this

    { fix m
      have "\<not> has_disc C m \<Longrightarrow> \<not> has_disc C (optimize_primitive_univ m)"
      by(induction m rule: optimize_primitive_univ.induct) simp_all
    } moreover { fix m 
      have "\<not> has_disc C m \<Longrightarrow> \<not> has_disc C (opt_MatchAny_match_expr m)"
      by(induction m rule: opt_MatchAny_match_expr.induct) simp_all
    } ultimately show "\<forall> m \<in> get_match ` set rs. \<not> has_disc C m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_strict rs). \<not> has_disc C m"
      using matchpred_rule[of "\<lambda>m. \<not> has_disc C m"] by fast
    
    { fix m
      {fix a
       have "optimize_primitive_univ (Match a) = Match a \<or> optimize_primitive_univ (Match a) = MatchAny"
        by(induction "(Match a)" rule: optimize_primitive_univ.induct) auto
      } note matcha_cases=this
      have "normalized_nnf_match m \<Longrightarrow> normalized_nnf_match (optimize_primitive_univ m)"
      apply(induction m rule: optimize_primitive_univ.induct)
      apply simp_all
      apply(case_tac m)
          apply(simp_all)
      apply(case_tac "optimize_primitive_univ (Match a) = Match a")
       apply(simp)
      apply(case_tac "optimize_primitive_univ (Match a) = MatchAny")
       apply(simp)
      
      
    } moreover { fix m 
      have "\<not> has_disc C m \<Longrightarrow> \<not> has_disc C (opt_MatchAny_match_expr m)"
    } ultimately show "\<forall> m \<in> get_match ` set rs. \<not> has_disc C m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_strict rs). \<not> has_disc C m"
      using matchpred_rule[of "\<lambda>m. \<not> has_disc C m"] by fast
  
  qed


definition transform_strict :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where 
    "transform_strict = optimize_matches opt_MatchAny_match_expr(*^^10)*) \<circ> normalize_rules_dnf \<circ> optimize_matches optimize_primitive_univ \<circ> rw_Reject \<circ> rm_LogEmpty"


theorem transform_strict: assumes goodrs: "good_ruleset rs" and wf\<alpha>: "wf_unknown_match_tac \<alpha>"
      shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>transform_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      and "simple_ruleset (transform_strict rs)"
      and "\<forall> r \<in> set (transform_strict rs). normalized_nnf_match (get_match r)"
  proof -
    let ?\<gamma>="(common_matcher, \<alpha>)"
    let ?fw="\<lambda>rs. approximating_bigstep_fun ?\<gamma> p rs s"
    from approximating_semantics_iff_fun_good_ruleset goodrs have 1: "?\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> ?fw rs = t" by fast

    let ?rs2="(rw_Reject (rm_LogEmpty rs))"
    from goodrs rmLogEmpty_rwReject_good_to_simple have simple_rs2: "simple_ruleset ?rs2" by blast

    let ?rs3="(optimize_matches optimize_primitive_univ ?rs2)"
    from simple_rs2 optimize_matches_simple_ruleset have simple_rs3: "simple_ruleset ?rs3" by auto

    let ?rs4="(normalize_rules_dnf ?rs3)"
    from simple_rs3 simple_ruleset_normalize_rules_dnf have simple_rs4: "simple_ruleset ?rs4" by auto
    {fix rs::"'a rule list"
      have "\<forall> r \<in> set (normalize_rules_dnf rs). normalized_nnf_match (get_match r)"
        apply(induction rs)
         apply(simp)
        apply(rename_tac r rs, case_tac r)
        using normalized_nnf_match_normalize_match by fastforce
      } hence normalized_rs4: "\<forall> r \<in> set ?rs4. normalized_nnf_match (get_match r)" by auto

    let ?rs5="optimize_matches opt_MatchAny_match_expr ?rs4"
    from simple_rs4 optimize_matches_simple_ruleset have simple_rs5: "simple_ruleset ?rs5" by auto
    { fix m::"'a match_expr"
      have "normalized_nnf_match m \<Longrightarrow> normalized_nnf_match (opt_MatchAny_match_expr m)"
        by(induction m rule: opt_MatchAny_match_expr.induct) (auto)
    } hence "\<forall>m. normalized_nnf_match m \<longrightarrow> normalized_nnf_match (opt_MatchAny_match_expr m)" by blast
    from optimize_matches_normalized_nnf_match[OF normalized_rs4 this] have normalized_rs5: "\<forall> r \<in> set ?rs5. normalized_nnf_match (get_match r)" .

    from approximating_semantics_iff_fun_good_ruleset simple_rs5 simple_imp_good_ruleset have 2: 
      "?fw ?rs5 = t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>transform_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      unfolding transform_strict_def by fastforce

    have "?fw rs = ?fw (rm_LogEmpty rs)" using rm_LogEmpty_fun_semantics[symmetric] by fast
    also have "\<dots> = ?fw ?rs2" using rw_Reject_fun_semantics wf\<alpha> by metis
    also have "\<dots> = ?fw ?rs3"
      apply(rule optimize_matches[symmetric])
      using optimize_primitive_univ_correct_matchexpr by force
    also have "\<dots> = ?fw ?rs4"
      apply(rule normalize_rules_dnf_correct[symmetric])
      using simple_rs3 by (metis good_imp_wf_ruleset simple_imp_good_ruleset)
    also have "\<dots> = ?fw ?rs5" by (metis optimize_matches_opt_MatchAny_match_expr) 
    finally have rs: "?fw rs = ?fw ?rs5" .
    
    from 1 2 rs show  "(common_matcher, \<alpha>),p\<turnstile> \<langle>transform_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t" by presburger

    from simple_rs5 show "simple_ruleset (transform_strict rs)"
      by(simp add: transform_strict_def)

    from normalized_rs5 show "\<forall> r \<in> set (transform_strict rs). normalized_nnf_match (get_match r)"  
      by(simp add: transform_strict_def)
  qed

end

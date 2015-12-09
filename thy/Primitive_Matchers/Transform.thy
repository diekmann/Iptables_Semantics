theory Transform
imports Common_Primitive_Lemmas
        "../Semantics_Ternary/Semantics_Ternary"
        "../Semantics_Ternary/Negation_Type_Matching"
        Ports_Normalize
        IpAddresses_Normalize
        Interfaces_Normalize
        Protocols_Normalize
        "../Common/Remdups_Rev"
        Interface_Replace
begin


section{*Optimizing primitives*}

(*TODO: compress_normalize_interfaces still only works for input interfaces, not Oiface*)


(*just a test to be sure we can combine them, even though they use different internal types*)
(*TODO: delete*)
lemma deleteme1: "f \<in> set [compress_normalize_interfaces,
                          compress_normalize_protocols] \<Longrightarrow>
       normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> normalized_nnf_match m'"
  apply(simp)
  apply(erule disjE)
   using compress_normalize_interfaces_nnf apply blast
  using compress_normalize_protocols_nnf apply blast
  done
lemma deleteme2: "f \<in> set [compress_normalize_interfaces,
                           compress_normalize_protocols] \<Longrightarrow>
       normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> matches (common_matcher, \<alpha>) m' a p = matches (common_matcher, \<alpha>) m a p"
  apply(simp)
  apply(erule disjE)
   using compress_normalize_interfaces_Some apply blast
  using compress_normalize_protocols_Some apply blast
  done
lemma "normalized_nnf_match m \<Longrightarrow>
compress_normalize_primitive_monad [compress_normalize_interfaces, compress_normalize_protocols] m = Some m' \<Longrightarrow>
matches (common_matcher, \<alpha>) m' a p = matches (common_matcher, \<alpha>) m a p"
apply(rule compress_normalize_primitive_monad[where fs="[compress_normalize_interfaces,
                compress_normalize_protocols]", of "(common_matcher, \<alpha>)" a p m m'])
   using deleteme1 deleteme2 by blast+
  


section{*Transforming rulesets*}

subsection{*Optimizations*}

lemma approximating_bigstep_fun_remdups_rev:
  "approximating_bigstep_fun \<gamma> p (remdups_rev rs) s = approximating_bigstep_fun \<gamma> p rs s"
  proof(induction \<gamma> p rs s rule: approximating_bigstep_fun.induct)
    case 1 thus ?case by(simp add: remdups_rev_def)
    next
    case 2 thus ?case by (simp add: Decision_approximating_bigstep_fun)
    next
    case (3 \<gamma> p m a rs) thus ?case
      proof(cases "matches \<gamma> m a p")
        case False with 3 show ?thesis
         by(simp add: remdups_rev_fst remdups_rev_removeAll not_matches_removeAll) 
        next
        case True
        { fix rs s
          have "approximating_bigstep_fun \<gamma> p (filter (op \<noteq> (Rule m Log)) rs) s = approximating_bigstep_fun \<gamma> p rs s"
          proof(induction \<gamma> p rs s rule: approximating_bigstep_fun_induct)
          qed(auto simp add: Decision_approximating_bigstep_fun split: action.split)
        } note helper_Log=this
        { fix rs s
          have "approximating_bigstep_fun \<gamma> p (filter (op \<noteq> (Rule m Empty)) rs) s = approximating_bigstep_fun \<gamma> p rs s"
          proof(induction \<gamma> p rs s rule: approximating_bigstep_fun_induct)
          qed(auto simp add: Decision_approximating_bigstep_fun split: action.split)
        } note helper_Empty=this
        from True 3 show ?thesis
          apply(simp add: remdups_rev_fst split: action.split)
          apply(safe)
             apply(simp_all)
           apply(simp_all add: remdups_rev_removeAll)
           apply(simp_all add: removeAll_filter_not_eq helper_Empty helper_Log)
          done
        qed
  qed

lemma remdups_rev_simplers: "simple_ruleset rs \<Longrightarrow> simple_ruleset (remdups_rev rs)"
  by(induction rs) (simp_all add: remdups_rev_def simple_ruleset_def)

lemma remdups_rev_preserve_matches: "\<forall> m \<in> get_match ` set rs. P m \<Longrightarrow> \<forall> m \<in> get_match ` set (remdups_rev rs). P m"
  by(induction rs) (simp_all add: remdups_rev_def simple_ruleset_def)


(*TODO: closure bounds*)


subsection{*Optimize and Normalize to NNF form*}

(*without normalize_rules_dnf, the result cannot be normalized as optimize_primitive_univ can contain MatchNot MatchAny*)
definition transform_optimize_dnf_strict :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where 
    "transform_optimize_dnf_strict = optimize_matches opt_MatchAny_match_expr \<circ> 
        normalize_rules_dnf \<circ> (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ))"


(*TODO move*)
(*TODO: simplifier loops with this lemma*)
lemma optimize_matches_fst: "optimize_matches f (r#rs) = optimize_matches f [r]@optimize_matches f rs"
by(cases r)(simp add: optimize_matches_def)
  

theorem transform_optimize_dnf_strict: assumes simplers: "simple_ruleset rs" and wf\<alpha>: "wf_unknown_match_tac \<alpha>"
      shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>transform_optimize_dnf_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      and "simple_ruleset (transform_optimize_dnf_strict rs)"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). \<not> has_disc disc m"
      and "\<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). normalized_nnf_match m"
      and "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). normalized_n_primitive disc_sel f m"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc neg m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). \<not> has_disc_negated disc neg m"
  proof -
    let ?\<gamma>="(common_matcher, \<alpha>)"
    let ?fw="\<lambda>rs. approximating_bigstep_fun ?\<gamma> p rs s"

    have simplers1: "simple_ruleset (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ) rs)"
      using simplers optimize_matches_simple_ruleset by (metis)

    show simplers_transform: "simple_ruleset (transform_optimize_dnf_strict rs)"
      unfolding transform_optimize_dnf_strict_def
      using simplers by (simp add: optimize_matches_simple_ruleset simple_ruleset_normalize_rules_dnf)

    have 1: "?\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> ?fw rs = t"
      using approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers]] by fast

    have "?fw rs = ?fw (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ) rs)"
      apply(rule optimize_matches[symmetric])
      using optimize_primitive_univ_correct_matchexpr opt_MatchAny_match_expr_correct by (metis comp_apply)
    also have "\<dots> = ?fw (normalize_rules_dnf (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ) rs))"
      apply(rule normalize_rules_dnf_correct[symmetric])
      using simplers1 by (metis good_imp_wf_ruleset simple_imp_good_ruleset)
    also have "\<dots> = ?fw (optimize_matches opt_MatchAny_match_expr (normalize_rules_dnf (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ) rs)))"
      apply(rule optimize_matches[symmetric])
      using opt_MatchAny_match_expr_correct by (metis)
    finally have rs: "?fw rs = ?fw (transform_optimize_dnf_strict rs)"
      unfolding transform_optimize_dnf_strict_def by(simp)

    have 2: "?fw (transform_optimize_dnf_strict rs) = t \<longleftrightarrow> ?\<gamma>,p\<turnstile> \<langle>transform_optimize_dnf_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t "
      using approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers_transform], symmetric] by fast
    from 1 2 rs show "?\<gamma>,p\<turnstile> \<langle>transform_optimize_dnf_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> ?\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t" by simp


    have tf1: "\<And>r rs. transform_optimize_dnf_strict (r#rs) =
      (optimize_matches opt_MatchAny_match_expr (normalize_rules_dnf (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ) [r])))@
        transform_optimize_dnf_strict rs"
      unfolding transform_optimize_dnf_strict_def
      apply(simp)
      apply(subst optimize_matches_fst)
      apply(simp add: normalize_rules_dnf_append optimize_matches_append)
      done

    --"if the individual optimization functions preserve a property, then the whole thing does"
    { fix P m
      assume p1: "\<forall>m. P m \<longrightarrow> P (optimize_primitive_univ m)"
      assume p2: "\<forall>m. P m \<longrightarrow> P (opt_MatchAny_match_expr m)"
      assume p3: "\<forall>m. P m \<longrightarrow> (\<forall>m' \<in> set (normalize_match m). P m')"
      { fix rs
        have "\<forall> m \<in> get_match ` set rs. P m \<Longrightarrow> \<forall> m \<in> get_match ` set (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ) rs). P m"
          apply(rule optimize_matches_preserves)
          using p1 p2 by simp (*1s*)
      } note opt1=this
      { fix rs
        have "\<forall> m \<in> get_match ` set rs. P m \<Longrightarrow> \<forall> m \<in> get_match ` set (normalize_rules_dnf rs). P m"
        apply(induction rs rule: normalize_rules_dnf.induct)
         apply(simp; fail)
        apply(simp)
        apply(safe)
         apply(simp_all)
        using p3 by(simp)
      } note opt2=this
      { fix rs
        have "\<forall> m \<in> get_match ` set rs. P m \<Longrightarrow> \<forall> m \<in> get_match ` set (optimize_matches opt_MatchAny_match_expr rs). P m"
          apply(rule optimize_matches_preserves)
          using p2  by simp (*1s*)
      } note opt3=this
      have "\<forall> m \<in> get_match ` set rs. P m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). P m"
        apply(subst transform_optimize_dnf_strict_def)
        apply(drule opt1)
        apply(drule opt2)
        apply(drule opt3)
        by simp
    } note matchpred_rule=this

    { fix m
      have "\<not> has_disc disc m \<Longrightarrow> \<not> has_disc disc (optimize_primitive_univ m)"
      by(induction m rule: optimize_primitive_univ.induct) (simp_all)
    }  moreover { fix m
      have "\<not> has_disc disc m \<longrightarrow> (\<forall>m' \<in> set (normalize_match m). \<not> has_disc disc m')"
      by(induction m rule: normalize_match.induct) (safe,auto) --"need safe, otherwise simplifier loops"
    } ultimately show "\<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). \<not> has_disc disc m"
      using not_has_disc_opt_MatchAny_match_expr matchpred_rule[of "\<lambda>m. \<not> has_disc disc m"] by fast

    { fix m
      have "\<not> has_disc_negated disc neg m \<Longrightarrow> \<not> has_disc_negated disc neg (optimize_primitive_univ m)"
      apply(induction disc neg m rule: has_disc_negated.induct)
            apply(simp_all)
      apply(rename_tac a)
      apply(subgoal_tac "optimize_primitive_univ (Match a) = Match a \<or> optimize_primitive_univ (Match a) = MatchAny")
       apply safe
        apply simp_all
      using optimize_primitive_univ_unchanged_primitives by blast
    }  with not_has_disc_negated_opt_MatchAny_match_expr not_has_disc_normalize_match show
      "\<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc neg m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). \<not> has_disc_negated disc neg m"
      using matchpred_rule[of "\<lambda>m. \<not> has_disc_negated disc neg m"] by fast
   
   { fix P a
     have "(optimize_primitive_univ (Match a)) = (Match a) \<or> (optimize_primitive_univ (Match a)) = MatchAny"
       by(induction "(Match a)" rule: optimize_primitive_univ.induct) (auto)
     hence "((optimize_primitive_univ (Match a)) = Match a \<Longrightarrow> P a) \<Longrightarrow> (optimize_primitive_univ (Match a) = MatchAny \<Longrightarrow> P a) \<Longrightarrow> P a" by blast
   } note optimize_primitive_univ_match_cases=this

   { fix m
      have "normalized_n_primitive disc_sel f m \<Longrightarrow> normalized_n_primitive disc_sel f (optimize_primitive_univ m)"
      apply(induction disc_sel f m rule: normalized_n_primitive.induct)
            apply(simp_all split: split_if_asm)
        apply(rule optimize_primitive_univ_match_cases, simp_all)+
      done
    }  moreover { fix m
      have "normalized_n_primitive disc_sel f m \<longrightarrow> (\<forall>m' \<in> set (normalize_match m). normalized_n_primitive disc_sel f  m')"
      apply(induction m rule: normalize_match.induct)
            apply(simp_all)[2]

          apply(case_tac disc_sel) --"no idea why the simplifier loops"
          apply(clarify)
          apply(simp)
          apply(clarify)
          apply(simp)

         apply(safe)
             apply(simp_all)
      done
    } ultimately show "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow> 
        \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). normalized_n_primitive disc_sel f m"
      using matchpred_rule[of "\<lambda>m. normalized_n_primitive disc_sel f m"] normalized_n_primitive_opt_MatchAny_match_expr by fast
    

    { fix rs::"common_primitive rule list"
      {  fix m::"common_primitive match_expr"
             have "normalized_nnf_match m \<Longrightarrow> normalized_nnf_match (opt_MatchAny_match_expr m)"
               by(induction m rule: opt_MatchAny_match_expr.induct) (simp_all)
      } note x=this
      from normalize_rules_dnf_normalized_nnf_match[of "rs"]
      have "\<forall>x \<in> set (normalize_rules_dnf rs). normalized_nnf_match (get_match x)" .
      (*TODO simplify proof?*)
      hence "\<forall>m \<in> get_match ` set (optimize_matches opt_MatchAny_match_expr (normalize_rules_dnf rs)). normalized_nnf_match m"
        apply -
        apply(rule optimize_matches_preserves)
        using x by blast
      hence "\<forall>x \<in> set (optimize_matches opt_MatchAny_match_expr (normalize_rules_dnf rs)). normalized_nnf_match (get_match x)" 
        by blast
    } 
    thus "\<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). normalized_nnf_match m"
      unfolding transform_optimize_dnf_strict_def by simp
      
  qed


subsection{*Abstracting over unknowns*}

definition transform_remove_unknowns_generic :: "('a, 'packet) match_tac \<Rightarrow> 'a rule list \<Rightarrow> 'a rule list" where 
    "transform_remove_unknowns_generic \<gamma> = optimize_matches_a (remove_unknowns_generic \<gamma>) "
theorem transform_remove_unknowns_generic:
   assumes simplers: "simple_ruleset rs" and wf\<alpha>: "wf_unknown_match_tac \<alpha>" and packet_independent_\<alpha>: "packet_independent_\<alpha> \<alpha>"
    shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>transform_remove_unknowns_generic (common_matcher, \<alpha>) rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      and "simple_ruleset (transform_remove_unknowns_generic (common_matcher, \<alpha>) rs)"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (common_matcher, \<alpha>) rs). \<not> has_disc disc m"
      and "\<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (common_matcher, \<alpha>) rs). \<not> has_unknowns common_matcher m"
      (*may return MatchNot MatchAny*)
      (*and "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (common_matcher, \<alpha>) rs). normalized_nnf_match m"*)
      and "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (common_matcher, \<alpha>) rs). normalized_n_primitive disc_sel f m"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc neg m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (common_matcher, \<alpha>) rs). \<not> has_disc_negated disc neg m"
  proof -
    let ?\<gamma>="(common_matcher, \<alpha>)"
    let ?fw="\<lambda>rs. approximating_bigstep_fun ?\<gamma> p rs s"

    show simplers1: "simple_ruleset (transform_remove_unknowns_generic ?\<gamma> rs)"
      unfolding transform_remove_unknowns_generic_def
      using simplers optimize_matches_a_simple_ruleset by blast

    show "?\<gamma>,p\<turnstile> \<langle>transform_remove_unknowns_generic ?\<gamma> rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> ?\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      unfolding approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers1]]
      unfolding approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers]]
      unfolding transform_remove_unknowns_generic_def
      using optimize_matches_a_simplers[OF simplers] remove_unknowns_generic by metis

    { fix a m
      have "\<not> has_disc disc m \<Longrightarrow> \<not> has_disc disc (remove_unknowns_generic ?\<gamma> a m)"
      by(induction ?\<gamma> a m rule: remove_unknowns_generic.induct) simp_all
    } thus "\<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic ?\<gamma> rs). \<not> has_disc disc m"
      unfolding transform_remove_unknowns_generic_def
      by(induction rs) (simp_all add: optimize_matches_a_def)

      { fix a m
        have "normalized_n_primitive disc_sel f m \<Longrightarrow> 
                normalized_n_primitive disc_sel f (remove_unknowns_generic ?\<gamma> a m)"
      by(induction ?\<gamma> a m rule: remove_unknowns_generic.induct) (simp_all,cases disc_sel, simp)
    } thus "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic ?\<gamma> rs). normalized_n_primitive disc_sel f m"
      unfolding transform_remove_unknowns_generic_def
      by(induction rs) (simp_all add: optimize_matches_a_def)

    from simplers show "\<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (common_matcher, \<alpha>) rs). \<not> has_unknowns common_matcher m"
      unfolding transform_remove_unknowns_generic_def
      apply -
      apply(rule optimize_matches_a_preserves)
      apply(rule remove_unknowns_generic_specification[OF _ packet_independent_\<alpha> packet_independent_\<beta>_unknown_common_matcher])
      apply(simp add: simple_ruleset_def)
      done

    { fix m a
      have "\<not> has_disc_negated disc neg m \<Longrightarrow> \<not> has_disc_negated disc neg (remove_unknowns_generic (common_matcher, \<alpha>) a m)"
        by(induction m rule:remove_unknowns_generic.induct)(simp_all)
    }
    thus "\<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc neg m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (common_matcher, \<alpha>) rs). \<not> has_disc_negated disc neg m"
      unfolding transform_remove_unknowns_generic_def
      apply(rule optimize_matches_a_preserves)
      by blast
qed


corollary transform_remove_unknowns_upper: defines "upper \<equiv> optimize_matches_a upper_closure_matchexpr"
   assumes simplers: "simple_ruleset rs"
    shows "(common_matcher, in_doubt_allow),p\<turnstile> \<langle>upper rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      and "simple_ruleset (upper rs)"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (upper rs). \<not> has_disc disc m"
      and "\<forall> m \<in> get_match ` set (upper rs). \<not> has_disc is_Extra m"
      and "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (upper rs). normalized_n_primitive disc_sel f m"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc neg m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (upper rs). \<not> has_disc_negated disc neg m"
proof -
  from simplers have upper: "upper rs = transform_remove_unknowns_generic (common_matcher, in_doubt_allow) rs"
    apply(simp add: transform_remove_unknowns_generic_def upper_def)
    apply(erule optimize_matches_a_simple_ruleset_eq)
    by (simp add: upper_closure_matchexpr_generic)
  
  with transform_remove_unknowns_generic[OF simplers wf_in_doubt_allow packet_independent_unknown_match_tacs(1), simplified upper_closure_matchexpr_generic]
    show "(common_matcher, in_doubt_allow),p\<turnstile> \<langle>upper rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t" 
      and "simple_ruleset (upper rs)"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (upper rs). \<not> has_disc disc m"
      and "\<forall> m \<in> get_match ` set (upper rs). \<not> has_disc is_Extra m"
      and "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (upper rs). normalized_n_primitive disc_sel f m"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc neg m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (upper rs). \<not> has_disc_negated disc neg m"
    apply -
         apply(simp;fail)
        apply(simp;fail)
       apply presburger
      using has_unknowns_common_matcher apply auto[1]
     apply (metis packet_independent_unknown_match_tacs(1) simplers transform_remove_unknowns_generic(5) wf_in_doubt_allow)
    by presburger
qed


(*copy&paste from transform_remove_unknowns_upper*)
corollary transform_remove_unknowns_lower: defines "lower \<equiv> optimize_matches_a lower_closure_matchexpr"
   assumes simplers: "simple_ruleset rs"
    shows "(common_matcher, in_doubt_deny),p\<turnstile> \<langle>lower rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, in_doubt_deny),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      and "simple_ruleset (lower rs)"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (lower rs). \<not> has_disc disc m"
      and "\<forall> m \<in> get_match ` set (lower rs). \<not> has_disc is_Extra m"
      and "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (lower rs). normalized_n_primitive disc_sel f m"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc neg m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (lower rs). \<not> has_disc_negated disc neg m"
proof -
  from simplers have upper: "lower rs = transform_remove_unknowns_generic (common_matcher, in_doubt_deny) rs"
    apply(simp add: transform_remove_unknowns_generic_def lower_def)
    apply(erule optimize_matches_a_simple_ruleset_eq)
    by (simp add: lower_closure_matchexpr_generic)
  
  with transform_remove_unknowns_generic[OF simplers wf_in_doubt_deny packet_independent_unknown_match_tacs(2), simplified lower_closure_matchexpr_generic]
    show "(common_matcher, in_doubt_deny),p\<turnstile> \<langle>lower rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, in_doubt_deny),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t" 
      and "simple_ruleset (lower rs)"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (lower rs). \<not> has_disc disc m"
      and "\<forall> m \<in> get_match ` set (lower rs). \<not> has_disc is_Extra m"
      and "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (lower rs). normalized_n_primitive disc_sel f m"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc neg m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (lower rs). \<not> has_disc_negated disc neg m"
    apply -
         apply(simp;fail)
        apply(simp;fail)
       apply presburger
      using has_unknowns_common_matcher apply auto[1]
     apply (metis packet_independent_unknown_match_tacs(2) simplers transform_remove_unknowns_generic(5) wf_in_doubt_deny)
    by presburger
qed



subsection{*Normalizing and Transforming Primitives*}

text{*Rewrite the primitives IPs and Ports such that can be used by the simple firewall.*}
definition transform_normalize_primitives :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where 
    "transform_normalize_primitives =
      normalize_rules normalize_dst_ips \<circ>
      normalize_rules normalize_src_ips \<circ>
      normalize_rules normalize_dst_ports \<circ>
      normalize_rules normalize_src_ports \<circ>
      optimize_matches_option compress_normalize_interfaces"
      (*TODO: protocols and stuff? *)
      (*TODO interfaces and protocols here?*)
      (*optimize_matches_option compress_normalize_interfaces probably not because it can introduce new interfaces
        the discriminators are pretty fucked up :( *)



 thm normalize_primitive_extract_preserves_unrelated_normalized_n_primitive
 lemma normalize_rules_preserves_unrelated_normalized_n_primitive:
   assumes "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m \<and> normalized_n_primitive (disc2, sel2) P m" 
       and "wf_disc_sel (disc1, sel1) C"
       and "\<forall>a. \<not> disc2 (C a)"
    shows "\<forall>m \<in> get_match ` set (normalize_rules (normalize_primitive_extract (disc1, sel1) C f) rs). normalized_nnf_match m \<and> normalized_n_primitive (disc2, sel2) P m"
    thm normalize_rules_preserves[where P="\<lambda>m. normalized_nnf_match m \<and> normalized_n_primitive  (disc2, sel2) P m"
        and f="normalize_primitive_extract (disc1, sel1) C f"]
    apply(rule normalize_rules_preserves[where P="\<lambda>m. normalized_nnf_match m \<and> normalized_n_primitive  (disc2, sel2) P m"
        and f="normalize_primitive_extract (disc1, sel1) C f"])
     using assms(1) apply(simp)
    apply(safe)
     using normalize_primitive_extract_preserves_nnf_normalized[OF _ assms(2)] apply fast
    using normalize_primitive_extract_preserves_unrelated_normalized_n_primitive[OF _ _ assms(2) assms(3)] by blast


  lemma normalize_rules_normalized_n_primitive:
   assumes "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m"
       and "\<forall>m. normalized_nnf_match m \<longrightarrow>
             (\<forall>m' \<in> set (normalize_primitive_extract (disc, sel) C f m). normalized_n_primitive (disc, sel) P m')"
    shows "\<forall>m \<in> get_match ` set (normalize_rules (normalize_primitive_extract (disc, sel) C f) rs).
           normalized_n_primitive (disc, sel) P m"
    apply(rule normalize_rules_property[where P=normalized_nnf_match and f="normalize_primitive_extract (disc, sel) C f"])
     using assms(1) apply simp
    using assms(2) by simp


(*the simplifier preferes this*)
(*TODO: move*)
(*TODO: \<And> instead of \<forall> ?*)
lemma optimize_matches_option_preserves':
  "\<forall> m \<in> set rs. P (get_match m) \<Longrightarrow> \<forall>m. P m \<longrightarrow> (\<forall>m'. f m = Some m' \<longrightarrow> P m') \<Longrightarrow> \<forall>m \<in> set (optimize_matches_option f rs). P (get_match m)"
  using optimize_matches_option_preserves[simplified] by metis
thm optimize_matches_option_preserves

(*TODO: generalize?*)
lemma optimize_matches_option_compress_normalize_interfaces_preserves_unrelated_normalized_n_primitive:
 assumes "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m \<and> normalized_n_primitive (disc2, sel2) P m" 
     and "\<forall>a. \<not> disc2 (IIface a)"
  shows "\<forall>m \<in> get_match ` set (optimize_matches_option compress_normalize_interfaces rs). normalized_nnf_match m \<and> normalized_n_primitive (disc2, sel2) P m"
  thm optimize_matches_option_preserves
  apply(rule optimize_matches_option_preserves[where P="\<lambda>m. normalized_nnf_match m \<and> normalized_n_primitive  (disc2, sel2) P m"
      and f="compress_normalize_interfaces"])
  thm compress_normalize_interfaces_preserves_normalized_n_primitive
  apply(rule_tac m="(get_match r)" and m'=m in compress_normalize_interfaces_preserves_normalized_n_primitive)
     apply(simp_all add: assms)
  done

theorem transform_normalize_primitives:
  -- "all discriminators which will not be normalized remain unchanged"
  defines "unchanged disc \<equiv> (\<forall>a. \<not> disc (Src_Ports a)) \<and> (\<forall>a. \<not> disc (Dst_Ports a)) \<and> (\<forall>a. \<not> disc (Src a)) \<and> (\<forall>a. \<not> disc (Dst a))"
      -- "also holds for these discriminators"
      and "changeddisc disc \<equiv> (\<forall>a. \<not> disc (IIface a)) \<or> disc = is_Iiface"
  assumes simplers: "simple_ruleset rs"
      and wf\<alpha>: "wf_unknown_match_tac \<alpha>"
      and normalized: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m"
  shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>transform_normalize_primitives rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
    and "simple_ruleset (transform_normalize_primitives rs)"
    and "unchanged disc1 \<Longrightarrow> changeddisc disc1 \<Longrightarrow>
           \<forall> m \<in> get_match ` set rs. \<not> has_disc disc1 m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). \<not> has_disc disc1 m"
    and "\<forall> m \<in> get_match ` set (transform_normalize_primitives rs). normalized_nnf_match m"
    and "\<forall> m \<in> get_match ` set (transform_normalize_primitives rs).
          normalized_src_ports m \<and> normalized_dst_ports m \<and> normalized_src_ips m \<and> normalized_dst_ips m"
    and "unchanged disc2 \<Longrightarrow> (\<forall>a. \<not> disc2 (IIface a)) \<Longrightarrow>
         \<forall> m \<in> get_match ` set rs. normalized_n_primitive (disc2, sel2) f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). normalized_n_primitive (disc2, sel2) f m"
    and "unchanged disc3 \<Longrightarrow> changeddisc disc3 \<Longrightarrow>
         \<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc3 False m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). \<not> has_disc_negated disc3 False m"
  proof -
    let ?\<gamma>="(common_matcher, \<alpha>)"
    let ?fw="\<lambda>rs. approximating_bigstep_fun ?\<gamma> p rs s"

    show simplers_t: "simple_ruleset (transform_normalize_primitives rs)"
      unfolding transform_normalize_primitives_def
      by(simp add: simple_ruleset_normalize_rules simplers optimize_matches_option_simple_ruleset)

      let ?rs0="optimize_matches_option compress_normalize_interfaces rs"
    let ?rs1="normalize_rules normalize_src_ports ?rs0"
    let ?rs2="normalize_rules normalize_dst_ports ?rs1"
    let ?rs3="normalize_rules normalize_src_ips ?rs2"
    let ?rs4="normalize_rules normalize_dst_ips ?rs3"

    have normalized_rs0: "\<forall>m \<in> get_match ` set ?rs0. normalized_nnf_match m"
      apply(rule optimize_matches_option_preserves)
      apply(rule compress_normalize_interfaces_nnf)
      by(simp_all add: normalized)
    from normalize_rules_primitive_extract_preserves_nnf_normalized[OF this wf_disc_sel_common_primitive(1)]
         normalize_src_ports_def normalize_ports_step_def
    have normalized_rs1: "\<forall>m \<in> get_match ` set ?rs1. normalized_nnf_match m" by presburger
    from normalize_rules_primitive_extract_preserves_nnf_normalized[OF this wf_disc_sel_common_primitive(2)]
         normalize_dst_ports_def normalize_ports_step_def
    have normalized_rs2: "\<forall>m \<in> get_match ` set ?rs2. normalized_nnf_match m" by presburger
    from normalize_rules_primitive_extract_preserves_nnf_normalized[OF this wf_disc_sel_common_primitive(3)]
         normalize_src_ips_def
    have normalized_rs3: "\<forall>m \<in> get_match ` set ?rs3. normalized_nnf_match m" by presburger
    from normalize_rules_primitive_extract_preserves_nnf_normalized[OF this wf_disc_sel_common_primitive(4)]
         normalize_dst_ips_def
    have normalized_rs4: "\<forall>m \<in> get_match ` set ?rs4. normalized_nnf_match m" by presburger
    thus "\<forall> m \<in> get_match ` set (transform_normalize_primitives rs). normalized_nnf_match m"
      unfolding transform_normalize_primitives_def by simp

    (*TODO: add this as generic simp rule somewhere? But simplifier loops? what to do?*)
    have local_simp: "\<And>rs1 rs2. approximating_bigstep_fun ?\<gamma> p rs1 s = approximating_bigstep_fun ?\<gamma> p rs2 s \<Longrightarrow>
      (approximating_bigstep_fun ?\<gamma> p rs1 s = t) = (approximating_bigstep_fun ?\<gamma> p rs2 s = t)" by simp

    show "?\<gamma>,p\<turnstile> \<langle>transform_normalize_primitives rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> ?\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
     unfolding approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers_t]]
     unfolding approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers]]
     unfolding transform_normalize_primitives_def
     apply(simp)
     apply(subst normalize_rules_match_list_semantics_3[of normalized_nnf_match])
        using normalize_dst_ips apply(simp; fail)
       using simplers simple_ruleset_normalize_rules optimize_matches_option_simple_ruleset apply blast
      using normalized_rs3 apply(simp; fail)
     apply(subst normalize_rules_match_list_semantics_3[of normalized_nnf_match])
        using normalize_src_ips apply(simp; fail)
       using simplers simple_ruleset_normalize_rules optimize_matches_option_simple_ruleset apply blast
      using normalized_rs2 apply(simp; fail)
     apply(subst normalize_rules_match_list_semantics_3[of normalized_nnf_match])
        using normalize_dst_ports apply(simp; fail)
       using simplers simple_ruleset_normalize_rules optimize_matches_option_simple_ruleset apply blast
      using normalized_rs1 apply(simp; fail)
     apply(subst normalize_rules_match_list_semantics_3[of normalized_nnf_match])
        using normalize_src_ports apply(simp; fail)
       using simplers simple_ruleset_normalize_rules optimize_matches_option_simple_ruleset apply blast
      using normalized_rs0 apply(simp; fail)
     apply(subst local_simp, simp_all)
     apply(rule optimize_matches_option_generic[where P="\<lambda> m a. normalized_nnf_match m"])
       apply(simp_all add: normalized compress_normalize_interfaces_Some compress_normalize_interfaces_None)
     done


    from normalize_src_ports_normalized_n_primitive
    have normalized_src_ports: "\<forall>m \<in> get_match ` set ?rs1. normalized_src_ports m"
    using normalize_rules_property[OF normalized_rs0, where f=normalize_src_ports and Q=normalized_src_ports] by fast
      (*why u no rule?*)
    from normalize_dst_ports_normalized_n_primitive
         normalize_rules_property[OF normalized_rs1, where f=normalize_dst_ports and Q=normalized_dst_ports]
    have normalized_dst_ports: "\<forall>m \<in> get_match ` set ?rs2.  normalized_dst_ports m" by fast
    from normalize_src_ips_normalized_n_primitive
         normalize_rules_property[OF normalized_rs2, where f=normalize_src_ips and Q=normalized_src_ips]
    have normalized_src_ips: "\<forall>m \<in> get_match ` set ?rs3.  normalized_src_ips m" by fast
    from normalize_dst_ips_normalized_n_primitive
         normalize_rules_property[OF normalized_rs3, where f=normalize_dst_ips and Q=normalized_dst_ips]
    have normalized_dst_ips: "\<forall>m \<in> get_match ` set ?rs4.  normalized_dst_ips m" by fast


    from normalize_rules_preserves_unrelated_normalized_n_primitive[of _ is_Src_Ports src_ports_sel "(\<lambda>pts. length pts \<le> 1)",
         folded normalized_src_ports_def2 normalize_ports_step_def]
    have preserve_normalized_src_ports: "\<And>rs disc sel C f. 
      \<forall>m\<in>get_match ` set rs. normalized_nnf_match m  \<Longrightarrow>
      \<forall>m\<in>get_match ` set rs. normalized_src_ports m \<Longrightarrow>
      wf_disc_sel (disc, sel) C \<Longrightarrow>
      \<forall>a. \<not> is_Src_Ports (C a) \<Longrightarrow>
      \<forall>m\<in>get_match ` set (normalize_rules (normalize_primitive_extract (disc, sel) C f) rs). normalized_src_ports m"
      by metis
    from preserve_normalized_src_ports[OF normalized_rs1 normalized_src_ports wf_disc_sel_common_primitive(2),
         where f="(\<lambda>me. map (\<lambda>pt. [pt]) (ipt_ports_compress me))",
         folded normalize_ports_step_def normalize_dst_ports_def]
    have normalized_src_ports_rs2: "\<forall>m \<in> get_match ` set ?rs2.  normalized_src_ports m" by force
    from preserve_normalized_src_ports[OF normalized_rs2 normalized_src_ports_rs2 wf_disc_sel_common_primitive(3),
         where f=ipt_ipv4range_compress, folded normalize_src_ips_def]
    have normalized_src_ports_rs3: "\<forall>m \<in> get_match ` set ?rs3.  normalized_src_ports m" by force
    from preserve_normalized_src_ports[OF normalized_rs3 normalized_src_ports_rs3 wf_disc_sel_common_primitive(4),
         where f=ipt_ipv4range_compress, folded normalize_dst_ips_def]
    have normalized_src_ports_rs4: "\<forall>m \<in> get_match ` set ?rs4.  normalized_src_ports m" by force

    from normalize_rules_preserves_unrelated_normalized_n_primitive[of _ is_Dst_Ports dst_ports_sel "(\<lambda>pts. length pts \<le> 1)",
         folded normalized_dst_ports_def2 normalize_ports_step_def]
    have preserve_normalized_dst_ports: "\<And>rs disc sel C f. 
      \<forall>m\<in>get_match ` set rs. normalized_nnf_match m  \<Longrightarrow>
      \<forall>m\<in>get_match ` set rs. normalized_dst_ports m \<Longrightarrow>
      wf_disc_sel (disc, sel) C \<Longrightarrow>
      \<forall>a. \<not> is_Dst_Ports (C a) \<Longrightarrow>
      \<forall>m\<in>get_match ` set (normalize_rules (normalize_primitive_extract (disc, sel) C f) rs). normalized_dst_ports m"
      by metis
    from preserve_normalized_dst_ports[OF normalized_rs2 normalized_dst_ports wf_disc_sel_common_primitive(3),
         where f1=ipt_ipv4range_compress, folded normalize_src_ips_def]
    have normalized_dst_ports_rs3: "\<forall>m \<in> get_match ` set ?rs3.  normalized_dst_ports m" by force
    from preserve_normalized_dst_ports[OF normalized_rs3 normalized_dst_ports_rs3 wf_disc_sel_common_primitive(4),
         where f1=ipt_ipv4range_compress, folded normalize_dst_ips_def]
    have normalized_dst_ports_rs4: "\<forall>m \<in> get_match ` set ?rs4.  normalized_dst_ports m" by force

    from normalize_rules_preserves_unrelated_normalized_n_primitive[of ?rs3 is_Src src_sel normalized_cidr_ip,
         OF _ wf_disc_sel_common_primitive(4),
         where f=ipt_ipv4range_compress, folded normalize_dst_ips_def normalized_src_ips_def2]
         normalized_rs3 normalized_src_ips
    have normalized_src_rs4: "\<forall>m \<in> get_match ` set ?rs4. normalized_src_ips m" by force
    from normalized_src_ports_rs4 normalized_dst_ports_rs4 normalized_src_rs4 normalized_dst_ips
    show "\<forall> m \<in> get_match ` set (transform_normalize_primitives rs).
          normalized_src_ports m \<and> normalized_dst_ports m \<and> normalized_src_ips m \<and> normalized_dst_ips m"
      unfolding transform_normalize_primitives_def by force
   

   show  "unchanged disc2 \<Longrightarrow> (\<forall>a. \<not> disc2 (IIface a)) \<Longrightarrow>
          \<forall> m \<in> get_match ` set rs. normalized_n_primitive (disc2, sel2) f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). normalized_n_primitive  (disc2, sel2) f m"
   unfolding unchanged_def
   proof(elim conjE)
     assume "\<forall>m\<in>get_match ` set rs. normalized_n_primitive  (disc2, sel2) f m"
     with normalized have a': "\<forall>m\<in>get_match ` set rs. normalized_nnf_match m \<and> normalized_n_primitive (disc2, sel2) f m" by blast

     assume a_Src_Ports: "\<forall>a. \<not> disc2 (Src_Ports a)"
     assume a_Dst_Ports: "\<forall>a. \<not> disc2 (Dst_Ports a)"
     assume a_Src: "\<forall>a. \<not> disc2 (Src a)"
     assume a_Dst: "\<forall>a. \<not> disc2 (Dst a)"
     assume a_IIface: "(\<forall>a. \<not> disc2 (IIface a))"


     from a_IIface
     have "\<forall>m\<in>get_match ` set ?rs0. normalized_n_primitive (disc2, sel2) f m"
      by (metis a' optimize_matches_option_compress_normalize_interfaces_preserves_unrelated_normalized_n_primitive) 
     with normalized_rs0 normalize_rules_preserves_unrelated_normalized_n_primitive[OF _ wf_disc_sel_common_primitive(1) a_Src_Ports,
       of ?rs0 sel2 f "(\<lambda>me. map (\<lambda>pt. [pt]) (ipt_ports_compress me))",
       folded normalize_src_ports_def normalize_ports_step_def]
     have "\<forall>m\<in>get_match ` set ?rs1. normalized_n_primitive (disc2, sel2) f m" by blast
     with normalized_rs1 normalize_rules_preserves_unrelated_normalized_n_primitive[OF _ wf_disc_sel_common_primitive(2) a_Dst_Ports,
       of ?rs1 sel2 f "(\<lambda>me. map (\<lambda>pt. [pt]) (ipt_ports_compress me))",
       folded normalize_dst_ports_def normalize_ports_step_def]
     have "\<forall>m\<in>get_match ` set ?rs2. normalized_n_primitive (disc2, sel2) f m" by blast
     with normalized_rs2 normalize_rules_preserves_unrelated_normalized_n_primitive[OF _ wf_disc_sel_common_primitive(3) a_Src,
       of ?rs2 sel2 f ipt_ipv4range_compress,
       folded normalize_src_ips_def]
     have "\<forall>m\<in>get_match ` set ?rs3. normalized_n_primitive (disc2, sel2) f m" by blast
     with normalized_rs3 normalize_rules_preserves_unrelated_normalized_n_primitive[OF _ wf_disc_sel_common_primitive(4) a_Dst,
       of ?rs3 sel2 f ipt_ipv4range_compress,
       folded normalize_dst_ips_def]
     have "\<forall>m\<in>get_match ` set ?rs4. normalized_n_primitive (disc2, sel2) f m" by blast
     thus ?thesis
       unfolding transform_normalize_primitives_def by simp
   qed


   { fix m and m' and disc::"(common_primitive \<Rightarrow> bool)" and sel::"(common_primitive \<Rightarrow> 'x)" and C'::" ('x \<Rightarrow> common_primitive)"
         and f'::"('x negation_type list \<Rightarrow> 'x list)"
     assume am: "\<not> has_disc disc1 m"
        and nm: "normalized_nnf_match m"
        and am': "m' \<in> set (normalize_primitive_extract (disc, sel) C' f' m)"
        and wfdiscsel: "wf_disc_sel (disc,sel) C'"
        and disc_different: "\<forall>a. \<not> disc1 (C' a)"

        (*from wfdiscsel disc_different have "\<forall>a. \<not> disc1 (C' a)"
          apply(simp add: wf_disc_sel.simps)*)

        from disc_different have af: "\<forall>spts. (\<forall>a \<in> Match ` C' ` set (f' spts). \<not> has_disc disc1 a)"
          by(simp)

        obtain as ms where asms: "primitive_extractor (disc, sel) m = (as, ms)" by fastforce

        from am' asms have "m' \<in> (\<lambda>spt. MatchAnd (Match (C' spt)) ms) ` set (f' as)"
          unfolding normalize_primitive_extract_def by(simp)
        hence goalrule:"\<forall>spt \<in> set (f' as). \<not> has_disc disc1 (Match (C' spt)) \<Longrightarrow> \<not> has_disc disc1 ms \<Longrightarrow> \<not> has_disc disc1 m'" by fastforce

        from am primitive_extractor_correct(4)[OF nm wfdiscsel asms] have 1: "\<not> has_disc disc1 ms" by simp
        from af have 2: "\<forall>spt \<in> set (f' as). \<not> has_disc disc1 (Match (C' spt))" by simp

        from goalrule[OF 2 1] have "\<not> has_disc disc1 m'" .
        moreover from nm have "normalized_nnf_match m'" by (metis am' normalize_primitive_extract_preserves_nnf_normalized wfdiscsel)
        ultimately have "\<not> has_disc disc1 m' \<and> normalized_nnf_match m'" by simp
   }
   hence x: "\<And>disc sel C' f'.  wf_disc_sel (disc, sel) C' \<Longrightarrow> \<forall>a. \<not> disc1 (C' a) \<Longrightarrow>
   \<forall>m. normalized_nnf_match m \<and> \<not> has_disc disc1 m \<longrightarrow> (\<forall>m'\<in>set (normalize_primitive_extract (disc, sel) C' f' m). normalized_nnf_match m' \<and> \<not> has_disc disc1 m')"
   by blast

   { assume "(\<forall>a. \<not> disc1 (IIface a)) \<or> disc1 = is_Iiface"
     hence "\<forall>m\<in>set rs. \<not> has_disc disc1 (get_match m) \<and> normalized_nnf_match (get_match m) \<Longrightarrow>
           \<forall>m\<in>set (optimize_matches_option compress_normalize_interfaces rs). normalized_nnf_match (get_match m) \<and> \<not> has_disc disc1 (get_match m)"
     apply -
     apply(rule optimize_matches_option_preserves')
      apply(simp; fail)
     apply(elim disjE)
      using compress_normalize_interfaces_hasdisc apply blast
     using compress_normalize_interfaces_nnf compress_normalize_interfaces_not_introduces_Iiface by blast
   } note y=this

   have "\<forall>a. \<not> disc1 (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc1 (Dst_Ports a) \<Longrightarrow> 
         \<forall>a. \<not> disc1 (Src a) \<Longrightarrow> \<forall>a. \<not> disc1 (Dst a) \<Longrightarrow>
         (\<forall>a. \<not> disc1 (IIface a)) \<or> disc1 = is_Iiface \<Longrightarrow>
         \<forall> m \<in> get_match ` set rs. \<not> has_disc disc1 m \<and> normalized_nnf_match m \<Longrightarrow>
    \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). normalized_nnf_match m \<and> \<not> has_disc disc1 m"
   unfolding transform_normalize_primitives_def
   apply(simp)
   apply(rule normalize_rules_preserves')+
       apply(rule y)
        apply(simp; fail)
       apply(simp; fail)
      using x[OF wf_disc_sel_common_primitive(1), 
             of "(\<lambda>me. map (\<lambda>pt. [pt]) (ipt_ports_compress me))",folded normalize_src_ports_def normalize_ports_step_def] apply blast
     using x[OF wf_disc_sel_common_primitive(2), 
            of "(\<lambda>me. map (\<lambda>pt. [pt]) (ipt_ports_compress me))",folded normalize_dst_ports_def normalize_ports_step_def] apply blast
    using x[OF wf_disc_sel_common_primitive(3), of ipt_ipv4range_compress,folded normalize_src_ips_def] apply blast
   using x[OF wf_disc_sel_common_primitive(4), of ipt_ipv4range_compress,folded normalize_dst_ips_def] apply blast
   done
   
   thus "unchanged disc1 \<Longrightarrow> changeddisc disc1 \<Longrightarrow>
    \<forall> m \<in> get_match ` set rs. \<not> has_disc disc1 m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). \<not> has_disc disc1 m"
   unfolding unchanged_def changeddisc_def using normalized by blast

   (*TODO: copy pasta*)
   (*TODO: add normalized condition to the preserves lemma?*)
   { fix m and m' and disc::"(common_primitive \<Rightarrow> bool)" and sel::"(common_primitive \<Rightarrow> 'x)" and C'::" ('x \<Rightarrow> common_primitive)"
         and f'::"('x negation_type list \<Rightarrow> 'x list)" and neg
     assume am: "\<not> has_disc_negated disc3 neg m"
        and nm: "normalized_nnf_match m"
        and am': "m' \<in> set (normalize_primitive_extract (disc, sel) C' f' m)"
        and wfdiscsel: "wf_disc_sel (disc,sel) C'"
        and disc_different: "\<forall>a. \<not> disc3 (C' a)"

        from disc_different have af: "\<forall>spts. (\<forall>a \<in> Match ` C' ` set (f' spts). \<not> has_disc disc3 a)"
          by(simp)

        obtain as ms where asms: "primitive_extractor (disc, sel) m = (as, ms)" by fastforce

        from am' asms have "m' \<in> (\<lambda>spt. MatchAnd (Match (C' spt)) ms) ` set (f' as)"
          unfolding normalize_primitive_extract_def by(simp)
        hence goalrule:"\<forall>spt \<in> set (f' as). \<not> has_disc_negated disc3 neg (Match (C' spt)) \<Longrightarrow>
            \<not> has_disc_negated disc3 neg ms \<Longrightarrow> \<not> has_disc_negated disc3 neg m'" by fastforce

        from am primitive_extractor_correct(6)[OF nm wfdiscsel asms] have 1: "\<not> has_disc_negated disc3 neg ms" by simp
        from af have 2: "\<forall>spt \<in> set (f' as). \<not> has_disc_negated disc3 neg (Match (C' spt))" by simp

        from goalrule[OF 2 1] have "\<not> has_disc_negated disc3 neg m'" .
        moreover from nm have "normalized_nnf_match m'" by (metis am' normalize_primitive_extract_preserves_nnf_normalized wfdiscsel)
        ultimately have "\<not> has_disc_negated disc3 neg m' \<and> normalized_nnf_match m'" by simp
   }
   hence x: "\<And>disc sel C' f'.  wf_disc_sel (disc, sel) C' \<Longrightarrow> \<forall>a. \<not> disc3 (C' a) \<Longrightarrow>
   \<forall>m. normalized_nnf_match m \<and> \<not> has_disc_negated disc3 False m \<longrightarrow>
    (\<forall>m'\<in>set (normalize_primitive_extract (disc, sel) C' f' m). normalized_nnf_match m' \<and> \<not> has_disc_negated disc3 False m')"
   by blast

  {  assume "(\<forall>a. \<not> disc3 (IIface a)) \<or> disc3 = is_Iiface"
     hence "\<forall>m\<in>set rs. \<not> has_disc_negated disc3 False (get_match m) \<and> normalized_nnf_match (get_match m) \<Longrightarrow>
           \<forall>m\<in>set (optimize_matches_option compress_normalize_interfaces rs). normalized_nnf_match (get_match m) \<and> \<not> has_disc_negated disc3 False (get_match m)"
     apply -
     apply(rule optimize_matches_option_preserves')
      apply(simp; fail)
     apply(elim disjE)
      using compress_normalize_interfaces_hasdisc_negated apply blast
     using compress_normalize_interfaces_nnf compress_normalize_interfaces_not_introduces_Iiface_negated by blast
   } note y=this

   have "\<forall>a. \<not> disc3 (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc3 (Dst_Ports a) \<Longrightarrow> 
         \<forall>a. \<not> disc3 (Src a) \<Longrightarrow> \<forall>a. \<not> disc3 (Dst a) \<Longrightarrow>
         (\<forall>a. \<not> disc3 (IIface a)) \<or> disc3 = is_Iiface \<Longrightarrow>
         \<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc3 False m \<and> normalized_nnf_match m \<Longrightarrow>
    \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). normalized_nnf_match m \<and> \<not> has_disc_negated disc3 False m"
   unfolding transform_normalize_primitives_def
   apply(simp)
   apply(rule normalize_rules_preserves')+
       apply(rule y)
        apply(simp; fail)
       apply(simp; fail)
      using x[OF wf_disc_sel_common_primitive(1), 
             of "(\<lambda>me. map (\<lambda>pt. [pt]) (ipt_ports_compress me))",folded normalize_src_ports_def normalize_ports_step_def] apply blast
     using x[OF wf_disc_sel_common_primitive(2), 
            of "(\<lambda>me. map (\<lambda>pt. [pt]) (ipt_ports_compress me))",folded normalize_dst_ports_def normalize_ports_step_def] apply blast
    using x[OF wf_disc_sel_common_primitive(3), of ipt_ipv4range_compress,folded normalize_src_ips_def] apply blast
   using x[OF wf_disc_sel_common_primitive(4), of ipt_ipv4range_compress,folded normalize_dst_ips_def] apply blast
   done

   thus "unchanged disc3 \<Longrightarrow> changeddisc disc3 \<Longrightarrow>
         \<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc3 False m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). \<not> has_disc_negated disc3 False m"
   unfolding unchanged_def changeddisc_def using normalized by blast
qed


theorem iiface_constrain:
  assumes simplers: "simple_ruleset rs"
      and normalized: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m"
      and wf_ipassmt: "ipassmt_sanity_nowildcards ipassmt"
      and nospoofing: "case ipassmt (Iface (p_iiface p)) of Some ips \<Rightarrow> p_src p \<in> ipv4cidr_union_set (set ips)"
  shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>optimize_matches (iiface_constrain ipassmt) rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
    and "simple_ruleset (optimize_matches (iiface_constrain ipassmt) rs)"
  proof -
    show simplers_t: "simple_ruleset (optimize_matches (iiface_constrain ipassmt) rs)"
      by (simp add: optimize_matches_simple_ruleset simplers)

    have my_arg_cong: "\<And>P Q. P s = Q s \<Longrightarrow> (P s = t) \<longleftrightarrow> (Q s = t)" by simp
    
    show "(common_matcher, \<alpha>),p\<turnstile> \<langle>optimize_matches (iiface_constrain ipassmt) rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
     unfolding approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers_t]]
     unfolding approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers]]
     apply(rule my_arg_cong)
     apply(rule optimize_matches_generic[where P="\<lambda> m _. normalized_nnf_match m"])
      apply(simp add: normalized)
     apply(rule matches_iiface_constrain)
       apply(simp_all add: wf_ipassmt nospoofing)
     done
qed

text{*In contrast to @{thm iiface_constrain}, this requires  @{const ipassmt_sanity_disjoint} and 
      as much stronger nospoof assumption: This assumption requires that the packet is actually in ipassmt!*}
theorem iiface_rewrite:
  assumes simplers: "simple_ruleset rs"
      and normalized: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m"
      and wf_ipassmt: "ipassmt_sanity_nowildcards ipassmt"
      and disjoint_ipassmt: "ipassmt_sanity_disjoint ipassmt"
      and nospoofing: "\<exists>ips. ipassmt (Iface (p_iiface p)) = Some ips \<and> p_src p \<in> ipv4cidr_union_set (set ips)"
  shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>optimize_matches (iiface_rewrite ipassmt) rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
    and "simple_ruleset (optimize_matches (iiface_rewrite ipassmt) rs)"
  proof -
    show simplers_t: "simple_ruleset (optimize_matches (iiface_rewrite ipassmt) rs)"
      by (simp add: optimize_matches_simple_ruleset simplers)

    --"packet must come from a defined interface!"
    from nospoofing have "Iface (p_iiface p) \<in> dom ipassmt" by blast

    have my_arg_cong: "\<And>P Q. P s = Q s \<Longrightarrow> (P s = t) \<longleftrightarrow> (Q s = t)" by simp
    
    show "(common_matcher, \<alpha>),p\<turnstile> \<langle>optimize_matches (iiface_rewrite ipassmt) rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
     unfolding approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers_t]]
     unfolding approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers]]
     apply(rule my_arg_cong)
     apply(rule optimize_matches_generic[where P="\<lambda> m _. normalized_nnf_match m"])
      apply(simp add: normalized)
     apply(rule matches_iiface_rewrite)
        apply(simp_all add: wf_ipassmt nospoofing disjoint_ipassmt)
     done
qed


(*
theorem try_interface_replaceby_srcip:
  assumes simplers: "simple_ruleset rs"
      and normalized: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m"
      and wf_ipassmt: "ipassmt_sanity_nowildcards ipassmt"
      and nospoofing: "\<exists>ips. ipassmt (Iface (p_iiface p)) = Some ips \<and> p_src p \<in> ipv4cidr_union_set (set ips)"
  shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>try_interface_replaceby_srcip ipassmt rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
    and "simple_ruleset (try_interface_replaceby_srcip ipassmt rs)"
  proof -
    let ?\<gamma>="(common_matcher, \<alpha>)"
    let ?fw="\<lambda>rs. approximating_bigstep_fun ?\<gamma> p rs s"

    show simplers_t: "simple_ruleset (try_interface_replaceby_srcip ipassmt rs)"
      by (simp add: try_interface_replaceby_srcip_def simple_ruleset_normalize_rules_dnf optimize_matches_simple_ruleset simplers)

    --"packet must come from a defined interface!"
    from nospoofing have "Iface (p_iiface p) \<in> dom ipassmt" by blast

    have my_arg_cong: "\<And>P Q. P s = Q s \<Longrightarrow> (P s = t) \<longleftrightarrow> (Q s = t)" by simp

    { assume disjoint: "ipassmt_sanity_disjoint (ipassmt_ignore_wildcard ipassmt)"
      
      have "?fw rs = ?fw (optimize_matches (iiface_rewrite (ipassmt_ignore_wildcard ipassmt)) rs)"
      apply(cases "ipassmt_ignore_wildcard ipassmt (Iface (p_iiface p))")
       defer
       apply(rule optimize_matches_generic[where P="\<lambda> m _. normalized_nnf_match m", symmetric])
        apply(simp add: normalized)
       apply(rule matches_iiface_rewrite)
          apply(simp_all add: wf_ipassmt ipassmt_sanity_nowildcards_ignore_wildcardD disjoint)
       using ipassmt_ignore_wildcard_the(2) nospoofing apply fastforce
      oops
    }

    have "ipassmt_sanity_disjoint (ipassmt_ignore_wildcard ipassmt) \<Longrightarrow>
    \<not> ipassmt_sanity_disjoint ipassmt \<Longrightarrow>
    approximating_bigstep_fun (common_matcher, \<alpha>) p
      (optimize_matches (iiface_constrain ipassmt) (normalize_rules_dnf (optimize_matches (iiface_rewrite (ipassmt_ignore_wildcard ipassmt)) rs))) s =
    approximating_bigstep_fun (common_matcher, \<alpha>) p rs s"
    apply -
    thm optimize_matches_generic
    apply(rule optimize_matches_generic[where P="\<lambda> m _. normalized_nnf_match m"])
     apply(simp add: normalized)
    apply(rule matches_iiface_rewrite)
       apply(simp_all add: wf_ipassmt nospoofing)
       oops
    
    show "(common_matcher, \<alpha>),p\<turnstile> \<langle>try_interface_replaceby_srcip ipassmt rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
     unfolding approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers_t]]
     unfolding approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers]]
     apply(rule my_arg_cong)
     apply(simp add: try_interface_replaceby_srcip_def)
     apply(intro conjI impI)
        apply(rule optimize_matches_generic[where P="\<lambda> m _. normalized_nnf_match m"])
         apply(simp add: normalized)
        apply(rule matches_iiface_rewrite)
           apply(simp_all add: wf_ipassmt nospoofing)
       defer
       apply(rule optimize_matches_generic[where P="\<lambda> m _. normalized_nnf_match m"])
        apply(simp add: normalized)
       apply(rule matches_iiface_rewrite)
          apply(simp_all add: wf_ipassmt nospoofing)
      apply(rule optimize_matches_generic[where P="\<lambda> m _. normalized_nnf_match m"])
       apply(simp add: normalized)
      apply(rule matches_iiface_constrain)
         apply(simp_all add: wf_ipassmt)
      using nospoofing apply fastforce
     (*case (optimize_matches (iiface_constrain ipassmt) (normalize_rules_dnf (optimize_matches (iiface_rewrite (ipassmt_ignore_wildcard ipassmt)) rs)))*)
     
     done
qed
*)



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
  and "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow> \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow>
        \<forall> r \<in> get_match ` set rs. \<not> has_disc disc r \<Longrightarrow> \<forall> r \<in> get_match ` set (upper_closure rs). \<not> has_disc disc r"
  and "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow> \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow>
        \<forall> r \<in> get_match ` set rs. \<not> has_disc_negated disc False r \<Longrightarrow> \<forall> r \<in> get_match ` set (upper_closure rs). \<not> has_disc_negated disc False r"
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
           apply(simp;fail)
          apply(simp;fail)
         apply blast
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
      

    show "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow> \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow>
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
       apply(simp;fail)
      apply blast
     apply(simp;fail)
    apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_allow], simp)
    apply(frule(1) transform_optimize_dnf_strict(3)[OF _ wf_in_doubt_allow, where disc=disc])
    apply(simp add: remdups_rev_set)
    done

    show"\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow> \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow>
        \<forall> r \<in> get_match ` set rs. \<not> has_disc_negated disc False r \<Longrightarrow> \<forall> r \<in> get_match ` set (upper_closure rs). \<not> has_disc_negated disc False r"
    using simplers
    unfolding upper_closure_def
    apply - 
    apply(frule(1) transform_remove_unknowns_upper(6)[where disc=disc])
    apply(drule transform_remove_unknowns_upper(2))
    apply(frule(1) transform_optimize_dnf_strict(6)[OF _ wf_in_doubt_allow, where disc=disc])
    apply(frule transform_optimize_dnf_strict(4)[OF _ wf_in_doubt_allow])
    apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_allow])
    apply(frule(1) transform_normalize_primitives(7)[OF _ wf_in_doubt_allow, of _ disc])
       apply(simp;fail)
      apply blast
     apply(simp;fail)
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


(*copy&paste from transform_upper_closure*)
lemma transform_lower_closure:
  assumes simplers: "simple_ruleset rs"
  -- "semantics are preserved"
  shows "(common_matcher, in_doubt_deny),p\<turnstile> \<langle>lower_closure rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, in_doubt_deny),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
  and "simple_ruleset (lower_closure rs)"
  -- "simple, normalized rules without unknowns"
  and "\<forall> m \<in> get_match ` set (lower_closure rs). normalized_nnf_match m \<and>
         normalized_src_ports m \<and>
         normalized_dst_ports m \<and>
         normalized_src_ips m \<and>
         normalized_dst_ips m \<and>
         \<not> has_disc is_Extra m"
  -- "no new primitives are introduced"
  and "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow> \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow>
        \<forall> r \<in> get_match ` set rs. \<not> has_disc disc r \<Longrightarrow> \<forall> r \<in> get_match ` set (lower_closure rs). \<not> has_disc disc r"
  and "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow> \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow>
        \<forall> r \<in> get_match ` set rs. \<not> has_disc_negated disc False r \<Longrightarrow> \<forall> r \<in> get_match ` set (lower_closure rs). \<not> has_disc_negated disc False r"
  proof -
    { fix m a
        have "Rule m a \<in> set (lower_closure rs) \<Longrightarrow>
            (a = action.Accept \<or> a = action.Drop) \<and>
             normalized_nnf_match m \<and>
             normalized_src_ports m \<and>
             normalized_dst_ports m \<and>
             normalized_src_ips m \<and>
             normalized_dst_ips m \<and>
              \<not> has_disc is_Extra m"
        using simplers
        unfolding lower_closure_def
        apply(simp add: remdups_rev_set)
        apply(frule transform_remove_unknowns_lower(4))
        apply(drule transform_remove_unknowns_lower(2))
        thm transform_optimize_dnf_strict[OF _ wf_in_doubt_deny]
        apply(frule(1) transform_optimize_dnf_strict(3)[OF _ wf_in_doubt_deny, where disc=is_Extra])
        apply(thin_tac "\<forall>m\<in>get_match ` set (optimize_matches_a lower_closure_matchexpr rs). \<not> has_disc is_Extra m")
        apply(frule transform_optimize_dnf_strict(4)[OF _ wf_in_doubt_deny])
        apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_deny])
        thm transform_normalize_primitives[OF _ wf_in_doubt_deny]
        apply(frule(1) transform_normalize_primitives(3)[OF _ wf_in_doubt_deny, of _ is_Extra])
           apply(simp;fail)
          apply(simp;fail)
         apply blast
        apply(thin_tac "\<forall>m\<in>get_match ` set (transform_optimize_dnf_strict (optimize_matches_a lower_closure_matchexpr rs)). \<not> has_disc is_Extra m")
        apply(frule(1) transform_normalize_primitives(5)[OF _ wf_in_doubt_deny])
        apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_deny], simp)
        thm transform_optimize_dnf_strict[OF _ wf_in_doubt_deny]
        apply(frule(1) transform_optimize_dnf_strict(3)[OF _ wf_in_doubt_deny, where disc=is_Extra])
        apply(frule transform_optimize_dnf_strict(4)[OF _ wf_in_doubt_deny])
        apply(frule transform_optimize_dnf_strict(5)[OF _ wf_in_doubt_deny, of _ "(is_Src_Ports, src_ports_sel)" "(\<lambda>pts. length pts \<le> 1)"])
         apply(simp add: normalized_src_ports_def2; fail)
        apply(frule transform_optimize_dnf_strict(5)[OF _ wf_in_doubt_deny, of _ "(is_Dst_Ports, dst_ports_sel)" "(\<lambda>pts. length pts \<le> 1)"])
         apply(simp add: normalized_dst_ports_def2; fail)
        apply(frule transform_optimize_dnf_strict(5)[OF _ wf_in_doubt_deny, of _ "(is_Src, src_sel)" normalized_cidr_ip])
         apply(simp add: normalized_src_ips_def2; fail)
        apply(frule transform_optimize_dnf_strict(5)[OF _ wf_in_doubt_deny, of _ "(is_Dst, dst_sel)" normalized_cidr_ip])
         apply(simp add: normalized_dst_ips_def2; fail)
        apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_deny])
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

    from 1 show "simple_ruleset (lower_closure rs)"
      apply(simp add: simple_ruleset_def)
      apply(clarify)
      apply(rename_tac r)
      apply(case_tac r)
      apply(simp)
      by blast


    from 1 show "\<forall> m \<in> get_match ` set (lower_closure rs). normalized_nnf_match m \<and>
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
      

    show "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow> \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow>
            \<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow> \<forall> m \<in> get_match ` set (lower_closure rs). \<not> has_disc disc m"
    using simplers
    unfolding lower_closure_def
    apply - 
    apply(frule(1) transform_remove_unknowns_lower(3)[where disc=disc])
    apply(drule transform_remove_unknowns_lower(2))
    apply(frule(1) transform_optimize_dnf_strict(3)[OF _ wf_in_doubt_deny, where disc=disc])
    apply(frule transform_optimize_dnf_strict(4)[OF _ wf_in_doubt_deny])
    apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_deny])
    apply(frule(1) transform_normalize_primitives(3)[OF _ wf_in_doubt_deny, of _ disc])
       apply(simp;fail)
      apply blast
     apply(simp;fail)
    apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_deny], simp)
    apply(frule(1) transform_optimize_dnf_strict(3)[OF _ wf_in_doubt_deny, where disc=disc])
    apply(simp add: remdups_rev_set)
    done

    show"\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow> \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow>
        \<forall> r \<in> get_match ` set rs. \<not> has_disc_negated disc False r \<Longrightarrow> \<forall> r \<in> get_match ` set (lower_closure rs). \<not> has_disc_negated disc False r"
    using simplers
    unfolding lower_closure_def
    apply - 
    apply(frule(1) transform_remove_unknowns_lower(6)[where disc=disc])
    apply(drule transform_remove_unknowns_lower(2))
    apply(frule(1) transform_optimize_dnf_strict(6)[OF _ wf_in_doubt_deny, where disc=disc])
    apply(frule transform_optimize_dnf_strict(4)[OF _ wf_in_doubt_deny])
    apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_deny])
    apply(frule(1) transform_normalize_primitives(7)[OF _ wf_in_doubt_deny, of _ disc])
       apply(simp;fail)
      apply blast
     apply blast
    apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_deny], simp)
    apply(frule(1) transform_optimize_dnf_strict(6)[OF _ wf_in_doubt_deny, where disc=disc])
    apply(simp add: remdups_rev_set)
    done

    show "(common_matcher, in_doubt_deny),p\<turnstile> \<langle>lower_closure rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, in_doubt_deny),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
    using simplers
    unfolding lower_closure_def
    apply -
    apply(frule transform_remove_unknowns_lower(1)[where p=p and s=s and t=t])
    apply(drule transform_remove_unknowns_lower(2))
    apply(frule transform_optimize_dnf_strict(1)[OF _ wf_in_doubt_deny, where p=p and s=s and t=t])
    apply(frule transform_optimize_dnf_strict(4)[OF _ wf_in_doubt_deny])
    apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_deny])
    apply(frule(1) transform_normalize_primitives(1)[OF _ wf_in_doubt_deny, where p=p and s=s and t=t])
    apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_deny], simp)
    apply(frule transform_optimize_dnf_strict(1)[OF _ wf_in_doubt_deny, where p=p and s=s and t=t])
    apply(drule transform_optimize_dnf_strict(2)[OF _ wf_in_doubt_deny])
    apply(simp)
    using approximating_bigstep_fun_remdups_rev
    by (simp add: approximating_bigstep_fun_remdups_rev approximating_semantics_iff_fun_good_ruleset remdups_rev_simplers simple_imp_good_ruleset) 
  qed



definition "iface_try_rewrite ipassmt rs \<equiv> if ipassmt_sanity_disjoint (map_of ipassmt) \<and> ipassmt_sanity_defined rs (map_of ipassmt) then
  optimize_matches (iiface_rewrite (map_of_ipassmt ipassmt)) rs
  else
  optimize_matches (iiface_constrain (map_of_ipassmt ipassmt)) rs"

theorem iface_try_rewrite:
  assumes simplers: "simple_ruleset rs"
      and normalized: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m"
      and wf_ipassmt1: "ipassmt_sanity_nowildcards (map_of ipassmt)" and wf_ipassmt2: "distinct (map fst ipassmt)"
      and nospoofing: "\<exists>ips. (map_of ipassmt) (Iface (p_iiface p)) = Some ips \<and> p_src p \<in> ipv4cidr_union_set (set ips)"
  shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>iface_try_rewrite ipassmt rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
  apply(simp add: iface_try_rewrite_def)
  apply(simp add: map_of_ipassmt_def wf_ipassmt1 wf_ipassmt2)
  apply(intro conjI impI)
   apply(elim conjE)
   using iiface_rewrite(1)[OF simplers normalized wf_ipassmt1 _ nospoofing] apply blast
  using iiface_constrain(1)[OF simplers normalized wf_ipassmt1] nospoofing apply force
  done
end

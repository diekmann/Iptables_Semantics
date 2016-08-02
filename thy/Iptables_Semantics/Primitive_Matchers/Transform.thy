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
        "../Semantics_Ternary/Optimizing"
begin


section\<open>Optimizing and normalizing primitives\<close>
(*TODO: cleanup*)


definition compress_normalize_besteffort
  :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr option" where
   "compress_normalize_besteffort m \<equiv> compress_normalize_primitive_monad
          [compress_normalize_protocols,
           compress_normalize_input_interfaces,
           compress_normalize_output_interfaces] m"  
  
context begin
  private lemma compress_normalize_besteffort_normalized:
  "f \<in> set [compress_normalize_protocols,
            compress_normalize_input_interfaces,
            compress_normalize_output_interfaces] \<Longrightarrow>
         normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> normalized_nnf_match m'"
    apply(simp)
    apply(elim disjE)
      using compress_normalize_protocols_nnf apply blast
     using compress_normalize_input_interfaces_nnf apply blast
    using compress_normalize_output_interfaces_nnf apply blast
    done
  private lemma compress_normalize_besteffort_matches:
    assumes generic: "primitive_matcher_generic \<beta>"
    shows "f \<in> set [compress_normalize_protocols,
                    compress_normalize_input_interfaces,
                    compress_normalize_output_interfaces] \<Longrightarrow>
           normalized_nnf_match m \<Longrightarrow>
           f m = Some m' \<Longrightarrow>
           matches (\<beta>, \<alpha>) m' a p = matches (\<beta>, \<alpha>) m a p"
    apply(simp)
    apply(elim disjE)
      using primitive_matcher_generic.compress_normalize_protocols_Some[OF generic] apply blast
     using compress_normalize_input_interfaces_Some[OF generic] apply blast
    using compress_normalize_output_interfaces_Some[OF generic] apply blast
    done
  
  
  lemma compress_normalize_besteffort_Some: 
    assumes generic: "primitive_matcher_generic \<beta>"
    shows "normalized_nnf_match m \<Longrightarrow>
           compress_normalize_besteffort m = Some m' \<Longrightarrow>
           matches (\<beta>, \<alpha>) m' a p = matches (\<beta>, \<alpha>) m a p"
    unfolding compress_normalize_besteffort_def
    apply(rule compress_normalize_primitive_monad)
    using compress_normalize_besteffort_normalized compress_normalize_besteffort_matches[OF generic] by blast+
  lemma compress_normalize_besteffort_None:
    assumes generic: "primitive_matcher_generic \<beta>"
    shows "normalized_nnf_match m \<Longrightarrow>
           compress_normalize_besteffort m = None \<Longrightarrow>
           \<not> matches (\<beta>, \<alpha>) m a p"
  proof -
   have notmatches: "f \<in> set [compress_normalize_protocols, compress_normalize_input_interfaces, compress_normalize_output_interfaces] \<Longrightarrow>
           normalized_nnf_match m \<Longrightarrow> f m = None \<Longrightarrow> \<not> matches (\<beta>, \<alpha>) m a p" for f m
      apply(simp)
      using primitive_matcher_generic.compress_normalize_protocols_None[OF generic]
            compress_normalize_input_interfaces_None[OF generic]
            compress_normalize_output_interfaces_None[OF generic] by blast
   show "normalized_nnf_match m \<Longrightarrow> compress_normalize_besteffort m = None \<Longrightarrow> \<not> matches (\<beta>, \<alpha>) m a p"
     unfolding compress_normalize_besteffort_def
     apply(rule compress_normalize_primitive_monad_None)
         using compress_normalize_besteffort_normalized
               compress_normalize_besteffort_matches[OF generic]
               notmatches by blast+
  qed 
  lemma compress_normalize_besteffort_nnf:
    "normalized_nnf_match m \<Longrightarrow>
     compress_normalize_besteffort m = Some m' \<Longrightarrow>
     normalized_nnf_match m'"
    unfolding compress_normalize_besteffort_def
    apply(rule compress_normalize_primitive_monad)
       using compress_normalize_besteffort_normalized
             compress_normalize_besteffort_matches[OF primitive_matcher_generic_common_matcher]
             by blast+
  
  lemma compress_normalize_besteffort_not_introduces_Iiface:
      "\<not> has_disc is_Iiface m \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_besteffort m = Some m' \<Longrightarrow>
       \<not> has_disc is_Iiface m'"
    unfolding compress_normalize_besteffort_def
    apply(rule compress_normalize_primitive_monad_preserves[THEN conjunct2])
        apply(drule(3) compress_normalize_besteffort_normalized)
       apply(auto dest: compress_normalize_input_interfaces_not_introduces_Iiface
                        compress_normalize_protocols_hasdisc
                        compress_normalize_output_interfaces_hasdisc)
    done
  lemma compress_normalize_besteffort_not_introduces_Oiface:
      "\<not> has_disc is_Oiface m \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_besteffort m = Some m' \<Longrightarrow>
       \<not> has_disc is_Oiface m'"
    unfolding compress_normalize_besteffort_def
    apply(rule compress_normalize_primitive_monad_preserves[THEN conjunct2])
        apply(drule(3) compress_normalize_besteffort_normalized)
       apply(auto dest: compress_normalize_output_interfaces_hasdisc
                        compress_normalize_output_interfaces_not_introduces_Oiface
                        compress_normalize_protocols_hasdisc
                        compress_normalize_input_interfaces_hasdisc)
    done
  lemma compress_normalize_besteffort_not_introduces_Prot:
      "\<not> has_disc is_Prot m \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_besteffort m = Some m' \<Longrightarrow>
       \<not> has_disc is_Prot m'"
    unfolding compress_normalize_besteffort_def
    apply(rule compress_normalize_primitive_monad_preserves[THEN conjunct2])
        apply(drule(3) compress_normalize_besteffort_normalized)
       apply(auto dest: compress_normalize_input_interfaces_hasdisc compress_normalize_protocols_not_introduces_Prot
             compress_normalize_output_interfaces_hasdisc)
    done
  
  lemma compress_normalize_besteffort_not_introduces_Iiface_negated:
      "\<not> has_disc_negated is_Iiface False m \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_besteffort m = Some m' \<Longrightarrow>
       \<not> has_disc_negated is_Iiface False m'"
    unfolding compress_normalize_besteffort_def
    apply(rule compress_normalize_primitive_monad_preserves[THEN conjunct2])
        apply(drule(3) compress_normalize_besteffort_normalized)
       apply(auto dest: compress_normalize_besteffort_normalized compress_normalize_input_interfaces_not_introduces_Iiface_negated
                        compress_normalize_protocols_hasdisc_negated
                        compress_normalize_output_interfaces_hasdisc_negated)
    done
  lemma compress_normalize_besteffort_not_introduces_Oiface_negated:
      "\<not> has_disc_negated is_Oiface False m \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_besteffort m = Some m' \<Longrightarrow>
       \<not> has_disc_negated is_Oiface False m'"
    unfolding compress_normalize_besteffort_def
    apply(rule compress_normalize_primitive_monad_preserves[THEN conjunct2])
        apply(drule(3) compress_normalize_besteffort_normalized)
       apply(auto dest: compress_normalize_output_interfaces_not_introduces_Oiface_negated
                        compress_normalize_input_interfaces_hasdisc_negated
                        compress_normalize_protocols_hasdisc_negated)
    done
  lemma compress_normalize_besteffort_not_introduces_Prot_negated:
      "\<not> has_disc_negated is_Prot False m \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_besteffort m = Some m' \<Longrightarrow>
       \<not> has_disc_negated is_Prot False m'"
    unfolding compress_normalize_besteffort_def
    apply(rule compress_normalize_primitive_monad_preserves[THEN conjunct2])
        apply(drule(3) compress_normalize_besteffort_normalized)
       apply(auto dest: compress_normalize_input_interfaces_hasdisc_negated
                        compress_normalize_protocols_not_introduces_Prot_negated
                        compress_normalize_output_interfaces_hasdisc_negated)
    done
  lemma compress_normalize_besteffort_hasdisc:
      "\<not> has_disc disc m \<Longrightarrow> (\<forall>a. \<not> disc (IIface a)) \<Longrightarrow> (\<forall>a. \<not> disc (OIface a)) \<Longrightarrow> (\<forall>a. \<not> disc (Prot a)) \<Longrightarrow>
       normalized_nnf_match m \<Longrightarrow> compress_normalize_besteffort m = Some m' \<Longrightarrow>
       normalized_nnf_match m' \<and> \<not> has_disc disc m'"
    unfolding compress_normalize_besteffort_def
    apply(rule compress_normalize_primitive_monad_preserves)
        apply(drule(3) compress_normalize_besteffort_normalized)
       apply(auto dest: compress_normalize_input_interfaces_hasdisc
                        compress_normalize_output_interfaces_hasdisc
                        compress_normalize_protocols_hasdisc)
    done
  lemma compress_normalize_besteffort_hasdisc_negated:
      "\<not> has_disc_negated disc neg m \<Longrightarrow>
       (\<forall>a. \<not> disc (IIface a)) \<Longrightarrow> (\<forall>a. \<not> disc (OIface a)) \<Longrightarrow> (\<forall>a. \<not> disc (Prot a)) \<Longrightarrow>
       normalized_nnf_match m \<Longrightarrow> compress_normalize_besteffort m = Some m' \<Longrightarrow>
       normalized_nnf_match m' \<and> \<not> has_disc_negated disc neg m'"
    unfolding compress_normalize_besteffort_def
    apply(rule compress_normalize_primitive_monad_preserves)
        apply(drule(3) compress_normalize_besteffort_normalized)
       apply(simp split: option.split_asm)
       using compress_normalize_input_interfaces_hasdisc_negated
             compress_normalize_output_interfaces_hasdisc_negated
             compress_normalize_protocols_hasdisc_negated apply blast
    apply simp_all
    done
  lemma compress_normalize_besteffort_preserves_normalized_n_primitive:
    "normalized_n_primitive (disc, sel) P m \<Longrightarrow>
     (\<forall>a. \<not> disc (IIface a)) \<Longrightarrow> (\<forall>a. \<not> disc (OIface a)) \<Longrightarrow> (\<forall>a. \<not> disc (Prot a)) \<Longrightarrow>
     normalized_nnf_match m \<Longrightarrow> compress_normalize_besteffort m = Some m' \<Longrightarrow>
     normalized_nnf_match m' \<and> normalized_n_primitive (disc, sel) P m'"
    unfolding compress_normalize_besteffort_def
    apply(rule compress_normalize_primitive_monad_preserves)
        apply(drule(3) compress_normalize_besteffort_normalized)
       apply(auto dest: compress_normalize_input_interfaces_preserves_normalized_n_primitive
             compress_normalize_output_interfaces_preserves_normalized_n_primitive
             compress_normalize_protocols_preserves_normalized_n_primitive)
    done
end

section\<open>Transforming rulesets\<close>

subsection\<open>Optimizations\<close>

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


subsection\<open>Optimize and Normalize to NNF form\<close>

(*without normalize_rules_dnf, the result cannot be normalized as optimize_primitive_univ can contain MatchNot MatchAny*)
definition transform_optimize_dnf_strict :: "'i::len common_primitive rule list \<Rightarrow> 'i common_primitive rule list" where 
    "transform_optimize_dnf_strict = cut_off_after_match_any \<circ>
        (optimize_matches opt_MatchAny_match_expr \<circ> 
        normalize_rules_dnf \<circ> (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ)))"


(*TODO move*)
(*TODO: simplifier loops with this lemma*)
lemma optimize_matches_fst: "optimize_matches f (r#rs) = optimize_matches f [r]@optimize_matches f rs"
by(cases r)(simp add: optimize_matches_def)
  

theorem transform_optimize_dnf_strict_structure:
  assumes simplers: "simple_ruleset rs" and wf\<alpha>: "wf_unknown_match_tac \<alpha>"
  shows "simple_ruleset (transform_optimize_dnf_strict rs)"
  and "\<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow>
          \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). \<not> has_disc disc m"
  and "\<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). normalized_nnf_match m"
  and "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
        \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). normalized_n_primitive disc_sel f m"
  and "\<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc neg m \<Longrightarrow>
        \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). \<not> has_disc_negated disc neg m"
  proof -
    show simplers_transform: "simple_ruleset (transform_optimize_dnf_strict rs)"
      unfolding transform_optimize_dnf_strict_def
      using simplers by (simp add: cut_off_after_match_any_simplers
          optimize_matches_simple_ruleset simple_ruleset_normalize_rules_dnf)

    def transform_optimize_dnf_strict_inner \<equiv>
        "optimize_matches (opt_MatchAny_match_expr :: 'a common_primitive match_expr \<Rightarrow> 'a common_primitive match_expr) \<circ> 
        normalize_rules_dnf \<circ> (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ))"
    have inner_outer: "transform_optimize_dnf_strict = (cut_off_after_match_any \<circ> transform_optimize_dnf_strict_inner)"
      by(auto simp add: transform_optimize_dnf_strict_def transform_optimize_dnf_strict_inner_def)
    have tf1: "\<And>r rs. transform_optimize_dnf_strict_inner (r#rs) =
      (optimize_matches opt_MatchAny_match_expr (normalize_rules_dnf (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ) [r])))@
        transform_optimize_dnf_strict_inner rs"
      unfolding transform_optimize_dnf_strict_inner_def
      apply(simp)
      apply(subst optimize_matches_fst)
      apply(simp add: normalize_rules_dnf_append optimize_matches_append)
      done

    --"if the individual optimization functions preserve a property, then the whole thing does"
    { fix P :: "'a::len common_primitive match_expr \<Rightarrow> bool"
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
          using p2 by simp (*1s*)
      } note opt3=this
      have "\<forall> m \<in> get_match ` set rs. P m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). P m"
        unfolding transform_optimize_dnf_strict_def
        apply(drule opt1)
        apply(drule opt2)
        apply(drule opt3)
        using cut_off_after_match_any_preserve_matches by auto
    } note matchpred_rule=this

    { fix m
      have "\<not> has_disc disc m \<Longrightarrow> \<not> has_disc disc (optimize_primitive_univ m)"
      by(induction m rule: optimize_primitive_univ.induct) (simp_all)
    }  moreover { fix m
      have "\<not> has_disc disc m \<longrightarrow> (\<forall>m' \<in> set (normalize_match m). \<not> has_disc disc m')"
        using normalize_match_preserves_nodisc by fast
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
   
   { fix P and a::"'a common_primitive"
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
      (*TODO: do I have this already somewhere? move!*)
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
    

    { fix rs::"'a::len common_primitive rule list"
      {  fix m::"'a::len common_primitive match_expr"
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
    from this have "\<forall> m \<in> get_match ` set (transform_optimize_dnf_strict_inner rs). normalized_nnf_match m"
      unfolding transform_optimize_dnf_strict_inner_def by simp
    thus "\<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). normalized_nnf_match m"
      unfolding inner_outer
      apply simp
      apply(rule cut_off_after_match_any_preserve_matches[simplified])
      .
  qed

theorem transform_optimize_dnf_strict:
  assumes simplers: "simple_ruleset rs" and wf\<alpha>: "wf_unknown_match_tac \<alpha>"
  shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>transform_optimize_dnf_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
  proof -
    let ?\<gamma>="(common_matcher, \<alpha>)"
    let ?fw="\<lambda>rs. approximating_bigstep_fun ?\<gamma> p rs s"

    have simplers_transform: "simple_ruleset (transform_optimize_dnf_strict rs)"
      unfolding transform_optimize_dnf_strict_def
      using simplers by (simp add: cut_off_after_match_any_simplers 
                                    optimize_matches_simple_ruleset simple_ruleset_normalize_rules_dnf)

    have simplers1: "simple_ruleset (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ) rs)"
      using simplers optimize_matches_simple_ruleset by (metis)

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
      unfolding transform_optimize_dnf_strict_def by(simp add: cut_off_after_match_any)

    have 2: "?fw (transform_optimize_dnf_strict rs) = t \<longleftrightarrow> ?\<gamma>,p\<turnstile> \<langle>transform_optimize_dnf_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t "
      using approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers_transform], symmetric] by fast
    from 1 2 rs show "?\<gamma>,p\<turnstile> \<langle>transform_optimize_dnf_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> ?\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t" by simp
qed


subsection\<open>Abstracting over unknowns\<close>

definition transform_remove_unknowns_generic
  :: "('a, 'packet) match_tac \<Rightarrow> 'a rule list \<Rightarrow> 'a rule list"
where 
    "transform_remove_unknowns_generic \<gamma> = optimize_matches_a (remove_unknowns_generic \<gamma>) "

theorem transform_remove_unknowns_generic:
  assumes simplers: "simple_ruleset rs"
      and wf\<alpha>: "wf_unknown_match_tac \<alpha>" and packet_independent_\<alpha>: "packet_independent_\<alpha> \<alpha>"
      and wf\<beta>: "packet_independent_\<beta>_unknown \<beta>"
    shows "(\<beta>, \<alpha>),p\<turnstile> \<langle>transform_remove_unknowns_generic (\<beta>, \<alpha>) rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (\<beta>, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      and "simple_ruleset (transform_remove_unknowns_generic (\<beta>, \<alpha>) rs)"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (\<beta>, \<alpha>) rs). \<not> has_disc disc m"
      and "\<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (\<beta>, \<alpha>) rs). \<not> has_unknowns \<beta> m"
      (*may return MatchNot MatchAny*)
      (*and "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (common_matcher, \<alpha>) rs). normalized_nnf_match m"*)
      and "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (\<beta>, \<alpha>) rs). normalized_n_primitive disc_sel f m"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc neg m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (\<beta>, \<alpha>) rs). \<not> has_disc_negated disc neg m"
  proof -
    let ?\<gamma>="(\<beta>, \<alpha>)"
    let ?fw="\<lambda>rs. approximating_bigstep_fun ?\<gamma> p rs s"

    show simplers1: "simple_ruleset (transform_remove_unknowns_generic ?\<gamma> rs)"
      unfolding transform_remove_unknowns_generic_def
      using simplers optimize_matches_a_simple_ruleset by blast

    show "?\<gamma>,p\<turnstile> \<langle>transform_remove_unknowns_generic ?\<gamma> rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> ?\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      unfolding approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers1]]
      unfolding approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers]]
      unfolding transform_remove_unknowns_generic_def
      using optimize_matches_a_simplers[OF simplers] remove_unknowns_generic by metis

      from remove_unknowns_generic_not_has_disc show
        "\<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic ?\<gamma> rs). \<not> has_disc disc m"
      unfolding transform_remove_unknowns_generic_def
      by(intro optimize_matches_a_preserves) blast

      from remove_unknowns_generic_normalized_n_primitive show
        "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
           \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic ?\<gamma> rs). normalized_n_primitive disc_sel f m"
      unfolding transform_remove_unknowns_generic_def
      by(intro optimize_matches_a_preserves) blast

    show "\<forall> m \<in> get_match ` set (transform_remove_unknowns_generic ?\<gamma> rs). \<not> has_unknowns \<beta> m"
      unfolding transform_remove_unknowns_generic_def
      apply(rule optimize_matches_a_preserves)
      apply(rule remove_unknowns_generic_specification[OF _ packet_independent_\<alpha> wf\<beta>])
      using simplers by(simp add: simple_ruleset_def)

    from remove_unknowns_generic_not_has_disc_negated show
      "\<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc neg m \<Longrightarrow>
         \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic ?\<gamma> rs). \<not> has_disc_negated disc neg m"
      unfolding transform_remove_unknowns_generic_def
      by(rule optimize_matches_a_preserves) blast
qed
thm transform_remove_unknowns_generic[OF _ _ _ packet_independent_\<beta>_unknown_common_matcher]


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

  note * = transform_remove_unknowns_generic[OF 
      simplers wf_in_doubt_allow packet_independent_unknown_match_tacs(1) packet_independent_\<beta>_unknown_common_matcher,
      simplified upper_closure_matchexpr_generic]

    from *(1)[where p = p]
    show "(common_matcher, in_doubt_allow),p\<turnstile> \<langle>upper rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      by(subst upper)
    from *(2) show "simple_ruleset (upper rs)" by(subst upper)
    from *(3) show "\<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (upper rs). \<not> has_disc disc m"
      by(subst upper) fast
    from *(4) show "\<forall> m \<in> get_match ` set (upper rs). \<not> has_disc is_Extra m" 
      apply(subst upper)
      using has_unknowns_common_matcher by auto
    from *(5) show "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (upper rs). normalized_n_primitive disc_sel f m" 
      apply(subst upper)
      using packet_independent_unknown_match_tacs(1) simplers
        transform_remove_unknowns_generic(5)[OF _ _ _ packet_independent_\<beta>_unknown_common_matcher] wf_in_doubt_allow
      by blast
    from *(6) show "\<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc neg m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (upper rs). \<not> has_disc_negated disc neg m"
      by(subst upper) fast
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
  from simplers have lower: "lower rs = transform_remove_unknowns_generic (common_matcher, in_doubt_deny) rs"
    apply(simp add: transform_remove_unknowns_generic_def lower_def)
    apply(erule optimize_matches_a_simple_ruleset_eq)
    by (simp add: lower_closure_matchexpr_generic)

  note * = transform_remove_unknowns_generic[OF 
      simplers wf_in_doubt_deny packet_independent_unknown_match_tacs(2) packet_independent_\<beta>_unknown_common_matcher,
      simplified lower_closure_matchexpr_generic]

    from *(1)[where p = p]
    show "(common_matcher, in_doubt_deny),p\<turnstile> \<langle>lower rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, in_doubt_deny),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t" 
      by(subst lower)
    from *(2) show "simple_ruleset (lower rs)" by(subst lower)
    from *(3) show "\<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (lower rs). \<not> has_disc disc m"
      by(subst lower) fast
    from *(4) show "\<forall> m \<in> get_match ` set (lower rs). \<not> has_disc is_Extra m" 
      apply(subst lower)
      using has_unknowns_common_matcher by auto
    from *(5) show "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (lower rs). normalized_n_primitive disc_sel f m" 
      apply(subst lower)
      using packet_independent_unknown_match_tacs(1) simplers
        transform_remove_unknowns_generic(5)[OF _ _ _ packet_independent_\<beta>_unknown_common_matcher] wf_in_doubt_deny
      by blast
    from *(6) show "\<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc neg m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (lower rs). \<not> has_disc_negated disc neg m"
      by(subst lower) fast
qed



subsection\<open>Normalizing and Transforming Primitives\<close>

text\<open>Rewrite the primitives IPs and Ports such that can be used by the simple firewall.\<close>
definition transform_normalize_primitives :: "'i::len common_primitive rule list \<Rightarrow> 'i common_primitive rule list" where 
    "transform_normalize_primitives =
      normalize_rules normalize_dst_ips \<circ>
      normalize_rules normalize_src_ips \<circ>
      normalize_rules normalize_dst_ports \<circ>
      normalize_rules normalize_src_ports \<circ>
      optimize_matches_option compress_normalize_besteffort"
      (*TODO: protocols and stuff? *)
      (*TODO interfaces and protocols here?*)
      (*optimize_matches_option compress_normalize_input_interfaces probably not because it can introduce new interfaces
        the discriminators are pretty fucked up :( *)
      
      (*IMPORTANT TODO: optimizing ports may introduce matches on protocols. optimize away impossible
          port/protocol matches!*)



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
(*TODO: move*)
lemma optimize_matches_option_compress_normalize_besteffort_preserves_unrelated_normalized_n_primitive:
 assumes "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m \<and> normalized_n_primitive (disc2, sel2) P m" 
     and "\<forall>a. \<not> disc2 (IIface a)" and "\<forall>a. \<not> disc2 (OIface a)" and "\<forall>a. \<not> disc2 (Prot a)"
  shows "\<forall>m \<in> get_match ` set (optimize_matches_option compress_normalize_besteffort rs). normalized_nnf_match m \<and> normalized_n_primitive (disc2, sel2) P m"
  thm optimize_matches_option_preserves
  apply(rule optimize_matches_option_preserves[where P="\<lambda>m. normalized_nnf_match m \<and> normalized_n_primitive  (disc2, sel2) P m"
      and f="compress_normalize_besteffort"])
  apply(rule_tac m="(get_match r)" and m'=m in compress_normalize_besteffort_preserves_normalized_n_primitive)
     apply(simp_all add: assms)
  done

theorem transform_normalize_primitives:
  -- "all discriminators which will not be normalized remain unchanged"
  defines "unchanged disc \<equiv> (\<forall>a. \<not> disc (Src_Ports a)) \<and> (\<forall>a. \<not> disc (Dst_Ports a)) \<and>
                             (\<forall>a. \<not> disc (Src a)) \<and> (\<forall>a. \<not> disc (Dst a))"
      -- \<open>also holds for these discriminators, but not for @{const Prot}, which might be changed\<close>
      and "changeddisc disc \<equiv> ((\<forall>a. \<not> disc (IIface a)) \<or> disc = is_Iiface) \<and>
                               ((\<forall>a. \<not> disc (OIface a)) \<or> disc = is_Oiface)"
                               (*port normalization may introduce new matches on protocols*)
  assumes simplers: "simple_ruleset (rs :: 'i::len common_primitive rule list)"
      and wf\<alpha>: "wf_unknown_match_tac \<alpha>"
      and normalized: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m"
  shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>transform_normalize_primitives rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
    and "simple_ruleset (transform_normalize_primitives rs)"
    and "unchanged disc1 \<Longrightarrow> changeddisc disc1 \<Longrightarrow> \<forall>a. \<not> disc1 (Prot a) \<Longrightarrow>
           \<forall> m \<in> get_match ` set rs. \<not> has_disc disc1 m \<Longrightarrow>
              \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). \<not> has_disc disc1 m"
    and "\<forall> m \<in> get_match ` set (transform_normalize_primitives rs). normalized_nnf_match m"
    and "\<forall> m \<in> get_match ` set (transform_normalize_primitives rs).
          normalized_src_ports m \<and> normalized_dst_ports m \<and> normalized_src_ips m \<and> normalized_dst_ips m"
    and "unchanged disc2 \<Longrightarrow> (\<forall>a. \<not> disc2 (IIface a)) \<Longrightarrow> (\<forall>a. \<not> disc2 (OIface a)) \<Longrightarrow> (\<forall>a. \<not> disc2 (Prot a)) \<Longrightarrow>
         \<forall> m \<in> get_match ` set rs. normalized_n_primitive (disc2, sel2) f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). normalized_n_primitive (disc2, sel2) f m"
    and "unchanged disc3 \<Longrightarrow> changeddisc disc3 \<Longrightarrow> \<forall>a. \<not> disc3 (Prot a) \<Longrightarrow>
         \<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc3 False m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). \<not> has_disc_negated disc3 False m"
  proof -
    let ?\<gamma>="(common_matcher, \<alpha>)"
    let ?fw="\<lambda>rs. approximating_bigstep_fun ?\<gamma> p rs s"

    show simplers_t: "simple_ruleset (transform_normalize_primitives rs)"
      unfolding transform_normalize_primitives_def
      by(simp add: simple_ruleset_normalize_rules simplers optimize_matches_option_simple_ruleset)

      let ?rs0="optimize_matches_option compress_normalize_besteffort rs"
    let ?rs1="normalize_rules normalize_src_ports ?rs0"
    let ?rs2="normalize_rules normalize_dst_ports ?rs1"
    let ?rs3="normalize_rules normalize_src_ips ?rs2"
    let ?rs4="normalize_rules normalize_dst_ips ?rs3"

    have normalized_rs0: "\<forall>m \<in> get_match ` set ?rs0. normalized_nnf_match m"
      apply(rule optimize_matches_option_preserves)
      apply(rule compress_normalize_besteffort_nnf)
      by(simp_all add: normalized)
    from normalize_src_ports_nnf have normalized_rs1: "\<forall>m \<in> get_match ` set ?rs1. normalized_nnf_match m"
      apply(intro normalize_rules_preserves[OF normalized_rs0])
      by blast
    from normalize_dst_ports_nnf have normalized_rs2: "\<forall>m \<in> get_match ` set ?rs2. normalized_nnf_match m"
      apply(intro normalize_rules_preserves[OF normalized_rs1])
      by blast
    from normalize_rules_primitive_extract_preserves_nnf_normalized[OF this wf_disc_sel_common_primitive(3)]
         normalize_src_ips_def
    have normalized_rs3: "\<forall>m \<in> get_match ` set ?rs3. normalized_nnf_match m" by metis
    from normalize_rules_primitive_extract_preserves_nnf_normalized[OF this wf_disc_sel_common_primitive(4)]
         normalize_dst_ips_def
    have normalized_rs4: "\<forall>m \<in> get_match ` set ?rs4. normalized_nnf_match m" by metis
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
        using normalize_dst_ips[where p = p] apply(simp; fail)
       using simplers simple_ruleset_normalize_rules optimize_matches_option_simple_ruleset apply blast
      using normalized_rs3 apply(simp; fail)
     apply(subst normalize_rules_match_list_semantics_3[of normalized_nnf_match])
        using normalize_src_ips[where p = p] apply(simp; fail)
       using simplers simple_ruleset_normalize_rules optimize_matches_option_simple_ruleset apply blast
      using normalized_rs2 apply(simp; fail)
     apply(subst normalize_rules_match_list_semantics_3[of normalized_nnf_match])
        using normalize_dst_ports[OF primitive_matcher_generic_common_matcher,where p = p] apply(simp; fail)
       using simplers simple_ruleset_normalize_rules optimize_matches_option_simple_ruleset apply blast
      using normalized_rs1 apply(simp; fail)
     apply(subst normalize_rules_match_list_semantics_3[of normalized_nnf_match])
        using normalize_src_ports[OF primitive_matcher_generic_common_matcher, where p = p] apply(simp; fail)
       using simplers simple_ruleset_normalize_rules optimize_matches_option_simple_ruleset apply blast
      using normalized_rs0 apply(simp; fail)
     apply(subst local_simp, simp_all)
     apply(rule optimize_matches_option_generic[where P="\<lambda> m a. normalized_nnf_match m"])
       apply(simp_all add: normalized
                  compress_normalize_besteffort_Some[OF primitive_matcher_generic_common_matcher]
                  compress_normalize_besteffort_None[OF primitive_matcher_generic_common_matcher])
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


    from normalize_rules_preserves_unrelated_normalized_n_primitive[of _ is_Src_Ports src_ports_sel "(\<lambda>ps. case ps of L4Ports _ pts \<Rightarrow> length pts \<le> 1)",
         folded normalized_src_ports_def2]
    have preserve_normalized_src_ports: " 
      \<forall>m\<in>get_match ` set rs. normalized_nnf_match m  \<Longrightarrow>
      \<forall>m\<in>get_match ` set rs. normalized_src_ports m \<Longrightarrow>
      wf_disc_sel (disc, sel) C \<Longrightarrow>
      \<forall>a. \<not> is_Src_Ports (C a) \<Longrightarrow>
      \<forall>m\<in>get_match ` set (normalize_rules (normalize_primitive_extract (disc, sel) C f) rs). normalized_src_ports m"
      for f :: "'c negation_type list \<Rightarrow> 'c list" and rs disc sel and C :: "'c \<Rightarrow> 'i::len common_primitive"
      by metis
    have normalized_src_ports_rs1: "\<forall>m \<in> get_match ` set ?rs1.  normalized_src_ports m"
      apply(rule normalize_rules_property[where P="normalized_nnf_match"])
       using normalized_rs0 apply blast
      using normalize_src_ports_normalized_n_primitive by blast
    (*from preserve_normalized_src_ports[OF normalized_rs1 normalized_src_ports wf_disc_sel_common_primitive(2),
         where f2 (* f *) = "(\<lambda>me. map (\<lambda>pt. [pt]) (raw_ports_compress me))",
         folded normalize_ports_step_def normalize_dst_ports_def]*)
    have normalize_dst_ports_preserves_normalized_src_ports:
      "m' \<in> set (normalize_dst_ports m) \<Longrightarrow> normalized_nnf_match m \<Longrightarrow>
        normalized_src_ports m \<Longrightarrow> normalized_src_ports m'" for m m' :: " 'i common_primitive match_expr"
      unfolding normalized_src_ports_def2
      apply(rule normalize_ports_generic_preserves_normalized_n_primitive[OF _ wf_disc_sel_common_primitive(2)])
           apply(simp_all)
      by (simp add: normalize_dst_ports_def normalize_ports_generic_def normalize_positive_dst_ports_def rewrite_negated_dst_ports_def)
    have normalized_src_ports_rs2: "\<forall>m \<in> get_match ` set ?rs2.  normalized_src_ports m"
      apply(rule normalize_rules_property[where P="\<lambda>m. normalized_nnf_match m \<and> normalized_src_ports m"])
       using normalized_rs1 normalized_src_ports_rs1 apply blast
      apply(clarify)
      using normalize_dst_ports_preserves_normalized_src_ports by blast
    from preserve_normalized_src_ports[OF normalized_rs2 normalized_src_ports_rs2 wf_disc_sel_common_primitive(3),
         where f2=ipt_iprange_compress, folded normalize_src_ips_def]
    have normalized_src_ports_rs3: "\<forall>m \<in> get_match ` set ?rs3.  normalized_src_ports m" by force
    from preserve_normalized_src_ports[OF normalized_rs3 normalized_src_ports_rs3 wf_disc_sel_common_primitive(4),
         where f2=ipt_iprange_compress, folded normalize_dst_ips_def]
    have normalized_src_ports_rs4: "\<forall>m \<in> get_match ` set ?rs4.  normalized_src_ports m" by force

    from normalize_rules_preserves_unrelated_normalized_n_primitive[of _ is_Dst_Ports dst_ports_sel "(\<lambda>ps. case ps of L4Ports _ pts \<Rightarrow> length pts \<le> 1)",
         folded normalized_dst_ports_def2]
    have preserve_normalized_dst_ports: "\<And>rs disc sel C f. 
      \<forall>m\<in>get_match ` set rs. normalized_nnf_match m  \<Longrightarrow>
      \<forall>m\<in>get_match ` set rs. normalized_dst_ports m \<Longrightarrow>
      wf_disc_sel (disc, sel) C \<Longrightarrow>
      \<forall>a. \<not> is_Dst_Ports (C a) \<Longrightarrow>
      \<forall>m\<in>get_match ` set (normalize_rules (normalize_primitive_extract (disc, sel) C f) rs). normalized_dst_ports m"
      by metis
    from preserve_normalized_dst_ports[OF normalized_rs2 normalized_dst_ports wf_disc_sel_common_primitive(3),
         where f2=ipt_iprange_compress, folded normalize_src_ips_def]
    have normalized_dst_ports_rs3: "\<forall>m \<in> get_match ` set ?rs3.  normalized_dst_ports m" by force
    from preserve_normalized_dst_ports[OF normalized_rs3 normalized_dst_ports_rs3 wf_disc_sel_common_primitive(4),
         where f2=ipt_iprange_compress, folded normalize_dst_ips_def]
    have normalized_dst_ports_rs4: "\<forall>m \<in> get_match ` set ?rs4.  normalized_dst_ports m" by force

    from normalize_rules_preserves_unrelated_normalized_n_primitive[of ?rs3 is_Src src_sel normalized_cidr_ip,
         OF _ wf_disc_sel_common_primitive(4),
         where f=ipt_iprange_compress, folded normalize_dst_ips_def normalized_src_ips_def2]
         normalized_rs3 normalized_src_ips
    have normalized_src_rs4: "\<forall>m \<in> get_match ` set ?rs4. normalized_src_ips m" by force
    from normalized_src_ports_rs4 normalized_dst_ports_rs4 normalized_src_rs4 normalized_dst_ips
    show "\<forall> m \<in> get_match ` set (transform_normalize_primitives rs).
          normalized_src_ports m \<and> normalized_dst_ports m \<and> normalized_src_ips m \<and> normalized_dst_ips m"
      unfolding transform_normalize_primitives_def by force
   

   show  "unchanged disc2 \<Longrightarrow> (\<forall>a. \<not> disc2 (IIface a)) \<Longrightarrow> (\<forall>a. \<not> disc2 (OIface a)) \<Longrightarrow> (\<forall>a. \<not> disc2 (Prot a)) \<Longrightarrow>
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
     assume a_OIface: "(\<forall>a. \<not> disc2 (OIface a))"
     assume a_Prot: "(\<forall>a. \<not> disc2 (Prot a))"


     from a_IIface a_OIface a_Prot
     have normalized_n_primitive_rs0: "\<forall>m\<in>get_match ` set ?rs0. normalized_n_primitive (disc2, sel2) f m"
      by (metis a' optimize_matches_option_compress_normalize_besteffort_preserves_unrelated_normalized_n_primitive) 
     with normalize_src_ports_preserves_normalized_n_primitive[OF _ a_Src_Ports] a_Prot have normalized_n_primitive_rs1:
     "\<forall>m\<in>get_match ` set ?rs1. normalized_n_primitive (disc2, sel2) f m" (*by blast*)
      apply(intro normalize_rules_property[where P="\<lambda>m. normalized_nnf_match m \<and> normalized_n_primitive (disc2, sel2) f m"])
       apply(simp)
       using normalized_rs0 apply blast
      by blast
     have "\<forall>m\<in>get_match ` set ?rs2. normalized_n_primitive (disc2, sel2) f m"
      apply(rule normalize_rules_property[where P="\<lambda>m. normalized_nnf_match m \<and> normalized_n_primitive (disc2, sel2) f m"])
       apply(simp)
       using normalized_n_primitive_rs1 normalized_rs1 apply blast
      using normalize_dst_ports_preserves_normalized_n_primitive[OF _ a_Dst_Ports] a_Prot by blast
     with normalized_rs2 normalize_rules_preserves_unrelated_normalized_n_primitive[OF _ wf_disc_sel_common_primitive(3) a_Src,
       of ?rs2 sel2 f ipt_iprange_compress,
       folded normalize_src_ips_def]
     have "\<forall>m\<in>get_match ` set ?rs3. normalized_n_primitive (disc2, sel2) f m" by blast
     with normalized_rs3 normalize_rules_preserves_unrelated_normalized_n_primitive[OF _ wf_disc_sel_common_primitive(4) a_Dst,
       of ?rs3 sel2 f ipt_iprange_compress,
       folded normalize_dst_ips_def]
     have "\<forall>m\<in>get_match ` set ?rs4. normalized_n_primitive (disc2, sel2) f m" by blast
     thus ?thesis
       unfolding transform_normalize_primitives_def by simp
   qed

   --"Pushing through properties through the ip normalizer"
   { fix m and m' and disc::"('i::len common_primitive \<Rightarrow> bool)"
         and sel::"('i::len common_primitive \<Rightarrow> 'x)" and C'::" ('x \<Rightarrow> 'i::len common_primitive)"
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
   hence x: "\<And>disc sel C' f'. wf_disc_sel (disc, sel) C' \<Longrightarrow> \<forall>a. \<not> disc1 (C' a) \<Longrightarrow>
   \<forall>m. normalized_nnf_match m \<and> \<not> has_disc disc1 m \<longrightarrow>
     (\<forall>m'\<in>set (normalize_primitive_extract (disc, sel) C' f' m). normalized_nnf_match m' \<and> \<not> has_disc disc1 m')"
   by blast

   --"Pushing through properties through the ports normalizer"
   from normalize_src_ports_preserves_normalized_not_has_disc normalize_src_ports_nnf have x_src_ports:
    "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow>  \<forall>a. \<not> disc (Prot a) \<Longrightarrow>  
       m' \<in> set (normalize_src_ports m) \<Longrightarrow>
            normalized_nnf_match m \<Longrightarrow> \<not> has_disc disc m \<Longrightarrow> normalized_nnf_match m' \<and> \<not> has_disc disc m'"
    for m m' and disc :: "'i common_primitive \<Rightarrow> bool" by blast
   from normalize_dst_ports_preserves_normalized_not_has_disc normalize_dst_ports_nnf have x_dst_ports:
    "\<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow>  \<forall>a. \<not> disc (Prot a) \<Longrightarrow>  
       m'\<in> set (normalize_dst_ports m) \<Longrightarrow>
          normalized_nnf_match m \<Longrightarrow> \<not> has_disc disc m \<Longrightarrow> normalized_nnf_match m' \<and> \<not> has_disc disc m'"
    for m m' and disc :: "'i common_primitive \<Rightarrow> bool"   by blast

   { assume "(\<forall>a. \<not> disc1 (IIface a)) \<or> disc1 = is_Iiface"
        and "((\<forall>a. \<not> disc1 (OIface a)) \<or> disc1 = is_Oiface)" and "(\<forall>a. \<not> disc1 (Prot a)) \<or> disc1 = is_Prot"
     hence "\<forall>m\<in>set rs. \<not> has_disc disc1 (get_match m) \<and> normalized_nnf_match (get_match m) \<Longrightarrow>
              \<forall>m\<in>set (optimize_matches_option compress_normalize_besteffort rs).
                  normalized_nnf_match (get_match m) \<and> \<not> has_disc disc1 (get_match m)"
     apply -
     apply(rule optimize_matches_option_preserves')
      apply(simp; fail)
     apply(elim disjE)
            using compress_normalize_besteffort_hasdisc apply blast
           using compress_normalize_besteffort_nnf compress_normalize_besteffort_not_introduces_Iiface compress_normalize_besteffort_not_introduces_Oiface
                 compress_normalize_besteffort_not_introduces_Prot by blast+
   } note y=this

   have "\<forall>a. \<not> disc1 (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc1 (Dst_Ports a) \<Longrightarrow> 
         \<forall>a. \<not> disc1 (Src a) \<Longrightarrow> \<forall>a. \<not> disc1 (Dst a) \<Longrightarrow>
         (\<forall>a. \<not> disc1 (IIface a)) \<or> disc1 = is_Iiface \<Longrightarrow>
         (\<forall>a. \<not> disc1 (OIface a)) \<or> disc1 = is_Oiface \<Longrightarrow> (\<forall>a. \<not> disc1 (Prot a)) (*\<or> disc1 = is_Prot*) \<Longrightarrow>
         \<forall> m \<in> get_match ` set rs. \<not> has_disc disc1 m \<and> normalized_nnf_match m \<Longrightarrow>
    \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). normalized_nnf_match m \<and> \<not> has_disc disc1 m"
   unfolding transform_normalize_primitives_def
   apply(simp)
   apply(rule normalize_rules_preserves')+
       apply(rule y)
          apply(simp; fail)
         apply(simp; fail)
        apply(simp; fail)
       apply(simp; fail)
      subgoal
      apply clarify
      by(rule x_src_ports) simp+
     subgoal
     apply clarify
     by(rule x_dst_ports) simp+
    using x[OF wf_disc_sel_common_primitive(3), of ipt_iprange_compress,folded normalize_src_ips_def] apply blast
   using x[OF wf_disc_sel_common_primitive(4), of ipt_iprange_compress,folded normalize_dst_ips_def] apply blast
   done
   
   thus "unchanged disc1 \<Longrightarrow> changeddisc disc1 \<Longrightarrow> \<forall>a. \<not> disc1 (Prot a) \<Longrightarrow>
    \<forall> m \<in> get_match ` set rs. \<not> has_disc disc1 m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). \<not> has_disc disc1 m"
   unfolding unchanged_def changeddisc_def using normalized by blast

   (*TODO: copy pasta*)
   (*TODO: add normalized condition to the preserves lemma?*)
   (*TODO: generalize for disc?*)
   { fix m and m' and disc::"('i::len common_primitive \<Rightarrow> bool)"
         and sel::"('i::len common_primitive \<Rightarrow> 'x)" and C'::" ('x \<Rightarrow> 'i::len common_primitive)"
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

   --"Pushing through properties through the ports normalizer"
   from normalize_src_ports_preserves_normalized_not_has_disc_negated normalize_src_ports_nnf have x_src_ports:
    "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> (\<forall>a. \<not> disc (Prot a)) \<or> \<not> has_disc_negated is_Src_Ports False m \<Longrightarrow>  
       m' \<in> set (normalize_src_ports m) \<Longrightarrow>
         normalized_nnf_match m \<Longrightarrow> \<not> has_disc_negated disc False m \<Longrightarrow>
            normalized_nnf_match m' \<and> \<not> has_disc_negated disc False m'"
    for m m' and disc :: "'i common_primitive \<Rightarrow> bool" by blast

   from normalize_dst_ports_preserves_normalized_not_has_disc_negated normalize_dst_ports_nnf have x_dst_ports:
    "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow>  \<forall>a. \<not> disc (Prot a) \<Longrightarrow>  
       m' \<in> set (normalize_dst_ports m) \<Longrightarrow>
         normalized_nnf_match m \<Longrightarrow> \<not> has_disc_negated disc False m \<Longrightarrow>
            normalized_nnf_match m' \<and> \<not> has_disc_negated disc False m'"
    for m m' and disc :: "'i common_primitive \<Rightarrow> bool" by blast

  {  assume "(\<forall>a. \<not> disc3 (IIface a)) \<or> disc3 = is_Iiface" and "(\<forall>a. \<not> disc3 (OIface a)) \<or> disc3 = is_Oiface" and "(\<forall>a. \<not> disc3 (Prot a)) \<or> disc3 = is_Prot"
     hence "\<forall>m\<in>set rs. \<not> has_disc_negated disc3 False (get_match m) \<and> normalized_nnf_match (get_match m) \<Longrightarrow>
           \<forall>m\<in>set (optimize_matches_option compress_normalize_besteffort rs). normalized_nnf_match (get_match m) \<and> \<not> has_disc_negated disc3 False (get_match m)"
     apply -
     apply(rule optimize_matches_option_preserves')
      apply(simp; fail)
     apply(elim disjE)
            using compress_normalize_besteffort_hasdisc_negated apply blast
           using compress_normalize_besteffort_nnf
                 compress_normalize_besteffort_not_introduces_Iiface_negated compress_normalize_besteffort_not_introduces_Oiface_negated
                 compress_normalize_besteffort_not_introduces_Prot_negated by blast+
   } note y=this

  
   have "\<forall>a. \<not> disc3 (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc3 (Dst_Ports a) \<Longrightarrow> 
         \<forall>a. \<not> disc3 (Src a) \<Longrightarrow> \<forall>a. \<not> disc3 (Dst a) \<Longrightarrow>
         (\<forall>a. \<not> disc3 (IIface a)) \<or> disc3 = is_Iiface \<Longrightarrow>
         (\<forall>a. \<not> disc3 (OIface a)) \<or> disc3 = is_Oiface \<Longrightarrow>
         (\<forall>a. \<not> disc3 (Prot a)) (*\<or>
          disc3 = is_Prot \<and> (\<forall>m \<in> get_match ` set rs.
            \<not> has_disc_negated is_Src_Ports False m \<and> \<not> has_disc_negated is_Dst_Ports False m)*) \<Longrightarrow>
         \<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc3 False m \<and> normalized_nnf_match m \<Longrightarrow>
    \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). normalized_nnf_match m \<and> \<not> has_disc_negated disc3 False m"
   unfolding transform_normalize_primitives_def
   apply(simp)
   apply(rule normalize_rules_preserves')+ (*this rule is just not good. we need to state that there could also be no negated ports or disc3 \<noteq> is_Prot*)
       apply(rule y)
          apply(simp; fail)
         apply(simp; fail)
        apply(blast)
       apply(simp; fail)
      subgoal
      apply(clarify)
      apply(rule_tac m5=m in x_src_ports)
          by(simp)+
     subgoal
     apply(clarify)
     by(rule x_dst_ports) simp+
    using x[OF wf_disc_sel_common_primitive(3), of ipt_iprange_compress,folded normalize_src_ips_def] apply blast
   using x[OF wf_disc_sel_common_primitive(4), of ipt_iprange_compress,folded normalize_dst_ips_def] apply blast
   done

   thus "unchanged disc3 \<Longrightarrow> changeddisc disc3 \<Longrightarrow> \<forall>a. \<not> disc3 (Prot a) \<Longrightarrow>
         \<forall> m \<in> get_match ` set rs. \<not> has_disc_negated disc3 False m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). \<not> has_disc_negated disc3 False m"
   unfolding unchanged_def changeddisc_def using normalized by blast
qed


theorem iiface_constrain:
  assumes simplers: "simple_ruleset rs"
      and normalized: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m"
      and wf_ipassmt: "ipassmt_sanity_nowildcards ipassmt"
      and nospoofing: "case ipassmt (Iface (p_iiface p)) of Some ips \<Rightarrow> p_src p \<in> ipcidr_union_set (set ips)"
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

text\<open>In contrast to @{thm iiface_constrain}, this requires  @{const ipassmt_sanity_disjoint} and 
      as much stronger nospoof assumption: This assumption requires that the packet is actually in ipassmt!\<close>
theorem iiface_rewrite:
  assumes simplers: "simple_ruleset rs"
      and normalized: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m"
      and wf_ipassmt: "ipassmt_sanity_nowildcards ipassmt"
      and disjoint_ipassmt: "ipassmt_sanity_disjoint ipassmt"
      and nospoofing: "\<exists>ips. ipassmt (Iface (p_iiface p)) = Some ips \<and> p_src p \<in> ipcidr_union_set (set ips)"
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



definition upper_closure :: "'i::len common_primitive rule list \<Rightarrow> 'i common_primitive rule list" where
  "upper_closure rs == remdups_rev (transform_optimize_dnf_strict
      (transform_normalize_primitives (transform_optimize_dnf_strict (optimize_matches_a upper_closure_matchexpr rs))))"
definition lower_closure :: "'i::len common_primitive rule list \<Rightarrow> 'i common_primitive rule list" where
  "lower_closure rs == remdups_rev (transform_optimize_dnf_strict
      (transform_normalize_primitives (transform_optimize_dnf_strict (optimize_matches_a lower_closure_matchexpr rs))))"


text\<open>putting it all together\<close>
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
       \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow> \<forall>a. \<not> disc (OIface a) \<or> disc = is_Oiface \<Longrightarrow>
       \<forall>a. \<not> disc (Prot a) (*\<or> disc = is_Prot*) \<Longrightarrow>
        \<forall> r \<in> get_match ` set rs. \<not> has_disc disc r \<Longrightarrow> \<forall> r \<in> get_match ` set (upper_closure rs). \<not> has_disc disc r"
  and "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow>
       \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow> \<forall>a. \<not> disc (OIface a) \<or> disc = is_Oiface \<Longrightarrow>
       \<forall>a. \<not> disc (Prot a) (*\<or>
        disc = is_Prot \<and>
        (\<forall> r \<in> get_match ` set rs. \<not> has_disc_negated is_Src_Ports False r \<and> \<not> has_disc_negated is_Dst_Ports False r)*) \<Longrightarrow>
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
        apply(frule(1) transform_optimize_dnf_strict_structure(2)[OF _ wf_in_doubt_allow, where disc=is_Extra])
        apply(thin_tac "\<forall>m\<in>get_match ` set (optimize_matches_a upper_closure_matchexpr rs). \<not> has_disc is_Extra m")
        apply(frule transform_optimize_dnf_strict_structure(3)[OF _ wf_in_doubt_allow])
        apply(drule transform_optimize_dnf_strict_structure(1)[OF _ wf_in_doubt_allow])
        thm transform_normalize_primitives[OF _ wf_in_doubt_allow]
        apply(frule(1) transform_normalize_primitives(3)[OF _ wf_in_doubt_allow, of _ is_Extra])
            apply(simp;fail)
           apply(simp;fail)
          apply(simp;fail)
         apply blast
        apply(thin_tac "\<forall>m\<in>get_match ` set (transform_optimize_dnf_strict (optimize_matches_a upper_closure_matchexpr rs)). \<not> has_disc is_Extra m")
        apply(frule(1) transform_normalize_primitives(5)[OF _ wf_in_doubt_allow])
        apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_allow], simp)
        thm transform_optimize_dnf_strict[OF _ wf_in_doubt_allow]
        apply(frule(1) transform_optimize_dnf_strict_structure(2)[OF _ wf_in_doubt_allow, where disc=is_Extra])
        apply(frule transform_optimize_dnf_strict_structure(3)[OF _ wf_in_doubt_allow])
        apply(frule transform_optimize_dnf_strict_structure(4)[OF _ wf_in_doubt_allow, of _ "(is_Src_Ports, src_ports_sel)" "(\<lambda>ps. case ps of L4Ports _ pts \<Rightarrow> length pts \<le> 1)"])
         apply(simp add: normalized_src_ports_def2; fail)
        apply(frule transform_optimize_dnf_strict_structure(4)[OF _ wf_in_doubt_allow, of _ "(is_Dst_Ports, dst_ports_sel)" "(\<lambda>ps. case ps of L4Ports _ pts \<Rightarrow> length pts \<le> 1)"])
         apply(simp add: normalized_dst_ports_def2; fail)
        apply(frule transform_optimize_dnf_strict_structure(4)[OF _ wf_in_doubt_allow, of _ "(is_Src, src_sel)" normalized_cidr_ip])
         apply(simp add: normalized_src_ips_def2; fail)
        apply(frule transform_optimize_dnf_strict_structure(4)[OF _ wf_in_doubt_allow, of _ "(is_Dst, dst_sel)" normalized_cidr_ip])
         apply(simp add: normalized_dst_ips_def2; fail)
        apply(drule transform_optimize_dnf_strict_structure(1)[OF _ wf_in_doubt_allow])
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
          \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow> \<forall>a. \<not> disc (OIface a) \<or> disc = is_Oiface \<Longrightarrow>
          \<forall>a. \<not> disc (Prot a) (*\<or> disc = is_Prot*) \<Longrightarrow>
            \<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow> \<forall> m \<in> get_match ` set (upper_closure rs). \<not> has_disc disc m"
    using simplers
    unfolding upper_closure_def
    apply - 
    apply(frule(1) transform_remove_unknowns_upper(3)[where disc=disc])
    apply(drule transform_remove_unknowns_upper(2))
    apply(frule(1) transform_optimize_dnf_strict_structure(2)[OF _ wf_in_doubt_allow, where disc=disc])
    apply(frule transform_optimize_dnf_strict_structure(3)[OF _ wf_in_doubt_allow])
    apply(drule transform_optimize_dnf_strict_structure(1)[OF _ wf_in_doubt_allow])
    apply(frule(1) transform_normalize_primitives(3)[OF _ wf_in_doubt_allow, of _ disc])
        apply(simp;fail)
       apply blast
      apply(simp;fail)
     apply(simp;fail)
    apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_allow], simp)
    apply(frule(1) transform_optimize_dnf_strict_structure(2)[OF _ wf_in_doubt_allow, where disc=disc])
    apply(simp add: remdups_rev_set)
    done

    show"\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow>
         \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow> \<forall>a. \<not> disc (OIface a) \<or> disc = is_Oiface \<Longrightarrow>
         \<forall>a. \<not> disc (Prot a) (*\<or> disc = is_Prot \<and> (\<forall> r \<in> get_match ` set rs. \<not> has_disc_negated is_Src_Ports False r \<and> \<not> has_disc_negated is_Dst_Ports False r)*) \<Longrightarrow>
        \<forall> r \<in> get_match ` set rs. \<not> has_disc_negated disc False r \<Longrightarrow> \<forall> r \<in> get_match ` set (upper_closure rs). \<not> has_disc_negated disc False r"
    using simplers
    unfolding upper_closure_def
    apply - 
    apply(frule(1) transform_remove_unknowns_upper(6)[where disc=disc])
    apply(drule transform_remove_unknowns_upper(2))
    apply(frule(1) transform_optimize_dnf_strict_structure(5)[OF _ wf_in_doubt_allow, where disc=disc])
    apply(frule transform_optimize_dnf_strict_structure(3)[OF _ wf_in_doubt_allow])
    apply(drule transform_optimize_dnf_strict_structure(1)[OF _ wf_in_doubt_allow])
    apply(frule(1) transform_normalize_primitives(7)[OF _ wf_in_doubt_allow, of _ disc])
        apply(simp;fail)
       apply blast
      apply(simp;fail)
     apply(simp;fail)
    apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_allow], simp)
    apply(frule(1) transform_optimize_dnf_strict_structure(5)[OF _ wf_in_doubt_allow, where disc=disc])
    apply(simp add: remdups_rev_set)
    done

    show "(common_matcher, in_doubt_allow),p\<turnstile> \<langle>upper_closure rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
    using simplers
    unfolding upper_closure_def
    apply -
    apply(frule transform_remove_unknowns_upper(1)[where p=p and s=s and t=t])
    apply(drule transform_remove_unknowns_upper(2))
    apply(frule transform_optimize_dnf_strict[OF _ wf_in_doubt_allow, where p=p and s=s and t=t])
    apply(frule transform_optimize_dnf_strict_structure(3)[OF _ wf_in_doubt_allow])
    apply(drule transform_optimize_dnf_strict_structure(1)[OF _ wf_in_doubt_allow])
    apply(frule(1) transform_normalize_primitives(1)[OF _ wf_in_doubt_allow, where p=p and s=s and t=t])
    apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_allow], simp)
    apply(frule transform_optimize_dnf_strict[OF _ wf_in_doubt_allow, where p=p and s=s and t=t])
    apply(drule transform_optimize_dnf_strict_structure(1)[OF _ wf_in_doubt_allow])
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
  and "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow>
       \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow> \<forall>a. \<not> disc (OIface a) \<or> disc = is_Oiface \<Longrightarrow>
       \<forall>a. \<not> disc (Prot a) (*\<or> disc = is_Prot*) \<Longrightarrow>
        \<forall> r \<in> get_match ` set rs. \<not> has_disc disc r \<Longrightarrow> \<forall> r \<in> get_match ` set (lower_closure rs). \<not> has_disc disc r"
  and "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow>
       \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow> \<forall>a. \<not> disc (OIface a) \<or> disc = is_Oiface \<Longrightarrow>
       \<forall>a. \<not> disc (Prot a) (*\<or> disc = is_Prot*) \<Longrightarrow>
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
        apply(frule(1) transform_optimize_dnf_strict_structure(2)[OF _ wf_in_doubt_deny, where disc=is_Extra])
        apply(thin_tac "\<forall>m\<in>get_match ` set (optimize_matches_a lower_closure_matchexpr rs). \<not> has_disc is_Extra m")
        apply(frule transform_optimize_dnf_strict_structure(3)[OF _ wf_in_doubt_deny])
        apply(drule transform_optimize_dnf_strict_structure(1)[OF _ wf_in_doubt_deny])
        thm transform_normalize_primitives[OF _ wf_in_doubt_deny]
        apply(frule(1) transform_normalize_primitives(3)[OF _ wf_in_doubt_deny, of _ is_Extra])
            apply(simp;fail)
           apply(simp;fail)
          apply(simp;fail)
         apply blast
        apply(thin_tac "\<forall>m\<in>get_match ` set (transform_optimize_dnf_strict (optimize_matches_a lower_closure_matchexpr rs)). \<not> has_disc is_Extra m")
        apply(frule(1) transform_normalize_primitives(5)[OF _ wf_in_doubt_deny])
        apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_deny], simp)
        thm transform_optimize_dnf_strict[OF _ wf_in_doubt_deny]
        apply(frule(1) transform_optimize_dnf_strict_structure(2)[OF _ wf_in_doubt_deny, where disc=is_Extra])
        apply(frule transform_optimize_dnf_strict_structure(3)[OF _ wf_in_doubt_deny])
        apply(frule transform_optimize_dnf_strict_structure(4)[OF _ wf_in_doubt_deny, of _ "(is_Src_Ports, src_ports_sel)" "(\<lambda>ps. case ps of L4Ports _ pts \<Rightarrow> length pts \<le> 1)"])
         apply(simp add: normalized_src_ports_def2; fail)
        apply(frule transform_optimize_dnf_strict_structure(4)[OF _ wf_in_doubt_deny, of _ "(is_Dst_Ports, dst_ports_sel)" "(\<lambda>ps. case ps of L4Ports _ pts \<Rightarrow> length pts \<le> 1)"])
         apply(simp add: normalized_dst_ports_def2; fail)
        apply(frule transform_optimize_dnf_strict_structure(4)[OF _ wf_in_doubt_deny, of _ "(is_Src, src_sel)" normalized_cidr_ip])
         apply(simp add: normalized_src_ips_def2; fail)
        apply(frule transform_optimize_dnf_strict_structure(4)[OF _ wf_in_doubt_deny, of _ "(is_Dst, dst_sel)" normalized_cidr_ip])
         apply(simp add: normalized_dst_ips_def2; fail)
        apply(drule transform_optimize_dnf_strict_structure(1)[OF _ wf_in_doubt_deny])
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
      

    show "\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow>
          \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow> \<forall>a. \<not> disc (OIface a) \<or> disc = is_Oiface \<Longrightarrow>
          \<forall>a. \<not> disc (Prot a) (*\<or> disc = is_Prot*) \<Longrightarrow>
            \<forall> m \<in> get_match ` set rs. \<not> has_disc disc m \<Longrightarrow> \<forall> m \<in> get_match ` set (lower_closure rs). \<not> has_disc disc m"
    using simplers
    unfolding lower_closure_def
    apply - 
    apply(frule(1) transform_remove_unknowns_lower(3)[where disc=disc])
    apply(drule transform_remove_unknowns_lower(2))
    apply(frule(1) transform_optimize_dnf_strict_structure(2)[OF _ wf_in_doubt_deny, where disc=disc])
    apply(frule transform_optimize_dnf_strict_structure(3)[OF _ wf_in_doubt_deny])
    apply(drule transform_optimize_dnf_strict_structure(1)[OF _ wf_in_doubt_deny])
    apply(frule(1) transform_normalize_primitives(3)[OF _ wf_in_doubt_deny, of _ disc])
        apply(simp;fail)
       apply blast
      apply(simp;fail)
     apply(simp;fail)
    apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_deny], simp)
    apply(frule(1) transform_optimize_dnf_strict_structure(2)[OF _ wf_in_doubt_deny, where disc=disc])
    apply(simp add: remdups_rev_set)
    done

    show"\<forall>a. \<not> disc (Src_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Dst_Ports a) \<Longrightarrow> \<forall>a. \<not> disc (Src a) \<Longrightarrow> \<forall>a. \<not> disc (Dst a) \<Longrightarrow>
         \<forall>a. \<not> disc (IIface a) \<or> disc = is_Iiface \<Longrightarrow> \<forall>a. \<not> disc (OIface a) \<or> disc = is_Oiface \<Longrightarrow>
         \<forall>a. \<not> disc (Prot a) (*\<or> disc = is_Prot*) \<Longrightarrow>
        \<forall> r \<in> get_match ` set rs. \<not> has_disc_negated disc False r \<Longrightarrow> \<forall> r \<in> get_match ` set (lower_closure rs). \<not> has_disc_negated disc False r"
    using simplers
    unfolding lower_closure_def
    apply - 
    apply(frule(1) transform_remove_unknowns_lower(6)[where disc=disc])
    apply(drule transform_remove_unknowns_lower(2))
    apply(frule(1) transform_optimize_dnf_strict_structure(5)[OF _ wf_in_doubt_deny, where disc=disc])
    apply(frule transform_optimize_dnf_strict_structure(3)[OF _ wf_in_doubt_deny])
    apply(drule transform_optimize_dnf_strict_structure(1)[OF _ wf_in_doubt_deny])
    apply(frule(1) transform_normalize_primitives(7)[OF _ wf_in_doubt_deny, of _ disc])
        apply(simp;fail)
       apply blast
      apply blast
     apply(simp;fail)
    apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_deny], simp)
    apply(frule(1) transform_optimize_dnf_strict_structure(5)[OF _ wf_in_doubt_deny, where disc=disc])
    apply(simp add: remdups_rev_set)
    done

    show "(common_matcher, in_doubt_deny),p\<turnstile> \<langle>lower_closure rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, in_doubt_deny),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
    using simplers
    unfolding lower_closure_def
    apply -
    apply(frule transform_remove_unknowns_lower(1)[where p=p and s=s and t=t])
    apply(drule transform_remove_unknowns_lower(2))
    apply(frule transform_optimize_dnf_strict[OF _ wf_in_doubt_deny, where p=p and s=s and t=t])
    apply(frule transform_optimize_dnf_strict_structure(3)[OF _ wf_in_doubt_deny])
    apply(drule transform_optimize_dnf_strict_structure(1)[OF _ wf_in_doubt_deny])
    apply(frule(1) transform_normalize_primitives(1)[OF _ wf_in_doubt_deny, where p=p and s=s and t=t])
    apply(drule transform_normalize_primitives(2)[OF _ wf_in_doubt_deny], simp)
    apply(frule transform_optimize_dnf_strict[OF _ wf_in_doubt_deny, where p=p and s=s and t=t])
    apply(drule transform_optimize_dnf_strict_structure(1)[OF _ wf_in_doubt_deny])
    apply(simp)
    using approximating_bigstep_fun_remdups_rev
    by (simp add: approximating_bigstep_fun_remdups_rev approximating_semantics_iff_fun_good_ruleset remdups_rev_simplers simple_imp_good_ruleset) 
  qed






theorem iface_try_rewrite:
  assumes simplers: "simple_ruleset rs"
      and normalized: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m"
      and wf_ipassmt1: "ipassmt_sanity_nowildcards (map_of ipassmt)" and wf_ipassmt2: "distinct (map fst ipassmt)"
      and nospoofing: "\<exists>ips. (map_of ipassmt) (Iface (p_iiface p)) = Some ips \<and> p_src p \<in> ipcidr_union_set (set ips)"
  shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>iface_try_rewrite ipassmt rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
proof -
  show "(common_matcher, \<alpha>),p\<turnstile> \<langle>iface_try_rewrite ipassmt rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
    apply(simp add: iface_try_rewrite_def)
    apply(simp add: map_of_ipassmt_def wf_ipassmt1 wf_ipassmt2)
    apply(intro conjI impI)
     apply(elim conjE)
     using iiface_rewrite(1)[OF simplers normalized wf_ipassmt1 _ nospoofing] apply blast
    using iiface_constrain(1)[OF simplers normalized wf_ipassmt1] nospoofing apply force
    done
qed


end

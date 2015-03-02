theory Transform
imports "Common_Primitive_Matcher"
        "../Semantics_Ternary"
        "../Output_Format/Negation_Type_Matching"
        "../Primitive_Matchers/Ports_Normalize"
        "../Primitive_Matchers/IpAddresses_Normalize"
begin

(*closure bounds*)

(*def: transform_optimize = optimize_matches opt_MatchAny_match_expr \<circ> optimize_matches optimize_primitive_univ
apply before and after initialization and closures
*)

(*without normalize_rules_dnf, the result cannot be normalized as optimize_primitive_univ can contain MatchNot MatchAny*)
definition transform_optimize_dnf_strict :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where 
    "transform_optimize_dnf_strict = optimize_matches opt_MatchAny_match_expr \<circ> 
        normalize_rules_dnf \<circ> (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ))"


(* TODO: move? *)
lemma normalized_n_primitive_opt_MatchAny_match_expr: "normalized_n_primitive disc_sel f m \<Longrightarrow> normalized_n_primitive disc_sel f (opt_MatchAny_match_expr m)"
  proof-
  { fix disc::"('a \<Rightarrow> bool)" and sel::"('a \<Rightarrow> 'b)" and n m1 m2
    have "normalized_n_primitive (disc, sel) n (opt_MatchAny_match_expr m1) \<Longrightarrow>
         normalized_n_primitive (disc, sel) n (opt_MatchAny_match_expr m2) \<Longrightarrow>
         normalized_n_primitive (disc, sel) n m1 \<and> normalized_n_primitive (disc, sel) n m2 \<Longrightarrow>
         normalized_n_primitive (disc, sel) n (opt_MatchAny_match_expr (MatchAnd m1 m2))"
  by(induction "(MatchAnd m1 m2)" rule: opt_MatchAny_match_expr.induct) (auto)
  }note x=this
  assume "normalized_n_primitive disc_sel f m"
  thus ?thesis
  apply(induction disc_sel f m rule: normalized_n_primitive.induct)
  apply simp_all
  using x by simp
  qed
  

theorem transform_optimize_dnf_strict: assumes simplers: "simple_ruleset rs" and wf\<alpha>: "wf_unknown_match_tac \<alpha>"
      shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>transform_optimize_dnf_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      and "simple_ruleset (transform_optimize_dnf_strict rs)"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc C m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). \<not> has_disc C m"
      and "\<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). normalized_nnf_match m"
      and "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). normalized_n_primitive disc_sel f m"
  proof -
    let ?\<gamma>="(common_matcher, \<alpha>)"
    let ?fw="\<lambda>rs. approximating_bigstep_fun ?\<gamma> p rs s"

    have simplers1: "simple_ruleset (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ) rs)"
      using simplers optimize_matches_simple_ruleset by (metis)

    show simplers_transform: "simple_ruleset (transform_optimize_dnf_strict rs)"
      unfolding transform_optimize_dnf_strict_def
      using simplers optimize_matches_simple_ruleset simple_ruleset_normalize_rules_dnf by (metis comp_apply)


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
      unfolding transform_optimize_dnf_strict_def by auto

    have 2: "?fw (transform_optimize_dnf_strict rs) = t \<longleftrightarrow> ?\<gamma>,p\<turnstile> \<langle>transform_optimize_dnf_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t "
      using approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers_transform], symmetric] by fast
    from 1 2 rs show "?\<gamma>,p\<turnstile> \<langle>transform_optimize_dnf_strict rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> ?\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t" by simp


    have tf1: "\<And>r rs. transform_optimize_dnf_strict (r#rs) =
      (optimize_matches opt_MatchAny_match_expr (normalize_rules_dnf (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ) [r])))@
        transform_optimize_dnf_strict rs"
      unfolding transform_optimize_dnf_strict_def by(simp add: optimize_matches_def)

    --"if the individual optimization functions preserve a property, then the whole thing does"
    { fix P m
      assume p1: "\<forall>m. P m \<longrightarrow> P (optimize_primitive_univ m)"
      assume p2: "\<forall>m. P m \<longrightarrow> P (opt_MatchAny_match_expr m)"
      assume p3: "\<forall>m. P m \<longrightarrow> (\<forall>m' \<in> set (normalize_match m). P m')"
      { fix rs
        have "\<forall> m \<in> get_match ` set rs. P m \<Longrightarrow> \<forall> m \<in> get_match ` set (optimize_matches (opt_MatchAny_match_expr \<circ> optimize_primitive_univ) rs). P m"
          apply(induction rs)
           apply(simp add: optimize_matches_def)
          apply(simp add: optimize_matches_def)
          using p1 p2 p3 by simp
      } note opt1=this
      have "\<forall> m \<in> get_match ` set rs. P m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). P m"
        apply(drule opt1)
        apply(induction rs)
         apply(simp add: optimize_matches_def transform_optimize_dnf_strict_def)
        apply(simp add: tf1 optimize_matches_def)
        apply(safe)
         apply(simp_all)
        using p1 p2 p3  by(simp)
    } note matchpred_rule=this

    { fix m
      have "\<not> has_disc C m \<Longrightarrow> \<not> has_disc C (optimize_primitive_univ m)"
      by(induction m rule: optimize_primitive_univ.induct) simp_all
    }  moreover { fix m 
      have "\<not> has_disc C m \<Longrightarrow> \<not> has_disc C (opt_MatchAny_match_expr m)"
      by(induction m rule: opt_MatchAny_match_expr.induct) simp_all
    }  moreover { fix m
      have "\<not> has_disc C m \<longrightarrow> (\<forall>m' \<in> set (normalize_match m). \<not> has_disc C m')"
      by(induction m rule: normalize_match.induct) (safe,auto) --"need safe, otherwise simplifier loops"
    } ultimately show "\<forall> m \<in> get_match ` set rs. \<not> has_disc C m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). \<not> has_disc C m"
      using matchpred_rule[of "\<lambda>m. \<not> has_disc C m"] by fast
   
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

          apply(case_tac disc_sel) --"no idea why the simplifier loops and this stuff and stuff and shit"
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
      hence "\<forall>x \<in> set (optimize_matches opt_MatchAny_match_expr (normalize_rules_dnf rs)). normalized_nnf_match (get_match x)" 
        apply(induction rs rule: normalize_rules_dnf.induct)
         apply(simp_all add: optimize_matches_def x)
        using x by fastforce
    } 
    thus "\<forall> m \<in> get_match ` set (transform_optimize_dnf_strict rs). normalized_nnf_match m"
      unfolding transform_optimize_dnf_strict_def by simp
      
  qed



(*TODO move?*)
lemma has_unknowns_common_matcher: "has_unknowns common_matcher m \<longleftrightarrow> has_disc is_Extra m"
  proof -
  { fix A p
    have "common_matcher A p = TernaryUnknown \<longleftrightarrow> is_Extra A"
      by(induction A p rule: common_matcher.induct) (simp_all add: bool_to_ternary_Unknown)
  } thus ?thesis
  by(induction common_matcher m rule: has_unknowns.induct) (simp_all)
qed

definition transform_remove_unknowns_generic :: "('a, 'packet) match_tac \<Rightarrow> 'a rule list \<Rightarrow> 'a rule list" where 
    "transform_remove_unknowns_generic \<gamma> = optimize_matches_a (remove_unknowns_generic \<gamma>) "
theorem transform_remove_unknowns_generic:
   assumes simplers: "simple_ruleset rs" and wf\<alpha>: "wf_unknown_match_tac \<alpha>" and packet_independent_\<alpha>: "packet_independent_\<alpha> \<alpha>"
    shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>transform_remove_unknowns_generic (common_matcher, \<alpha>) rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
      and "simple_ruleset (transform_remove_unknowns_generic (common_matcher, \<alpha>) rs)"
      and "\<forall> m \<in> get_match ` set rs. \<not> has_disc C m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (common_matcher, \<alpha>) rs). \<not> has_disc C m"
      and "\<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (common_matcher, \<alpha>) rs). \<not> has_unknowns common_matcher m"
      (*may return MatchNot MatchAny*)
      (*and "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (common_matcher, \<alpha>) rs). normalized_nnf_match m"*)
      and "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic (common_matcher, \<alpha>) rs). normalized_n_primitive disc_sel f m"
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
      have "\<not> has_disc C m \<Longrightarrow> \<not> has_disc C (remove_unknowns_generic ?\<gamma> a m)"
      by(induction ?\<gamma> a m rule: remove_unknowns_generic.induct) simp_all
    } thus "\<forall> m \<in> get_match ` set rs. \<not> has_disc C m \<Longrightarrow>
            \<forall> m \<in> get_match ` set (transform_remove_unknowns_generic ?\<gamma> rs). \<not> has_disc C m"
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
      apply(induction rs)
       apply(simp add: optimize_matches_a_def)
      apply(simp add: optimize_matches_a_def simple_ruleset_tail)
      apply(rule remove_unknowns_generic_specification[OF _ packet_independent_\<alpha> packet_independent_\<beta>_unknown_common_matcher])
      apply(simp add: simple_ruleset_def)
      done
qed





(* TODO *)
definition transform_normalize_primitives :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where 
    "transform_normalize_primitives =
      normalize_rules normalize_dst_ips \<circ>
      normalize_rules normalize_src_ips \<circ>
      normalize_rules normalize_dst_ports \<circ>
      normalize_rules normalize_src_ports"


 (*TODO: move*)
 (*tuned version for usage with normalize_primitive_extract*)
 lemma normalize_rules_match_list_semantics_3: 
    assumes "\<forall>m a. normalized_nnf_match m \<longrightarrow> match_list \<gamma> (f m) a p = matches \<gamma> m a p"
    and "simple_ruleset rs"
    and normalized: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m"
    shows "approximating_bigstep_fun \<gamma> p (normalize_rules f rs) s = approximating_bigstep_fun \<gamma> p rs s"
    apply(rule normalize_rules_match_list_semantics_2)
     using normalized assms(1) apply blast
    using assms(2) by simp
    

 (*TODO: move and*)
  lemma normalize_rules_primitive_extract_preserves_nnf_normalized: "\<forall>m\<in>get_match ` set rs. normalized_nnf_match m \<Longrightarrow> wf_disc_sel disc_sel C \<Longrightarrow>
     \<forall>m\<in>get_match ` set (normalize_rules (normalize_primitive_extract disc_sel C f) rs). normalized_nnf_match m"
  apply(rule normalize_rules_preserves[where P="normalized_nnf_match" and f="(normalize_primitive_extract disc_sel C f)"])
   apply(simp)
  apply(cases disc_sel)
  using normalize_primitive_extract_preserves_nnf_normalized by fast


 thm normalize_primitive_extract_preserves_unrelated_normalized_n_primitive
 lemma normalize_rules_preserves_unrelated_normalized_n_primitive:
   assumes "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m \<and> normalized_n_primitive (disc2, sel2) P m" 
       and "wf_disc_sel (disc1, sel1) C"
       and "\<forall>a. \<not> disc2 (C a)"
       and "\<forall>m. normalized_nnf_match m \<longrightarrow> normalized_n_primitive (disc2, sel2) P2 m \<longrightarrow>
                (\<forall>m' \<in> set (normalize_primitive_extract (disc1, sel1) C f m). normalized_n_primitive (disc2, sel2) P m')"
    shows "\<forall>m \<in> get_match ` set (normalize_rules (normalize_primitive_extract (disc1, sel1) C f) rs). normalized_nnf_match m \<and> normalized_n_primitive (disc2, sel2) P m"
    thm normalize_rules_preserves[where P="\<lambda>m. normalized_nnf_match m \<and> normalized_n_primitive  (disc2, sel2) P m"
        and f="normalize_primitive_extract (disc1, sel1) C f"]
    apply(rule normalize_rules_preserves[where P="\<lambda>m. normalized_nnf_match m \<and> normalized_n_primitive  (disc2, sel2) P m"
        and f="normalize_primitive_extract (disc1, sel1) C f"])
     using assms(1) apply(simp)
    apply(safe)
     using normalize_primitive_extract_preserves_nnf_normalized[OF _ assms(2)] apply fast
    using normalize_primitive_extract_preserves_unrelated_normalized_n_primitive[OF _ _ assms(2) assms(3)] by blast




theorem transform_normalize_primitives:
  assumes simplers: "simple_ruleset rs"
      and wf\<alpha>: "wf_unknown_match_tac \<alpha>"
      and normalized: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m"
  shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>transform_normalize_primitives rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
    and "simple_ruleset (transform_normalize_primitives rs)"
    and "\<forall> m \<in> get_match ` set rs. \<not> has_disc C m \<Longrightarrow> \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). \<not> has_disc C m"
    and "\<forall> m \<in> get_match ` set (transform_normalize_primitives rs). normalized_nnf_match m"
    and "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
          \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). normalized_n_primitive disc_sel f m"
  proof -
    let ?\<gamma>="(common_matcher, \<alpha>)"
    let ?fw="\<lambda>rs. approximating_bigstep_fun ?\<gamma> p rs s"

    show simplers_t: "simple_ruleset (transform_normalize_primitives rs)"
      unfolding transform_normalize_primitives_def
      by(simp add: simple_ruleset_normalize_rules simplers)

    from normalize_rules_primitive_extract_preserves_nnf_normalized[OF normalized wf_disc_sel_common_primitive(1)]
         normalize_src_ports_def normalize_ports_step_def
    have normalized_result1: "\<forall>m \<in> get_match ` set (normalize_rules normalize_src_ports rs).
            normalized_nnf_match m" by presburger
    from normalize_rules_primitive_extract_preserves_nnf_normalized[OF this wf_disc_sel_common_primitive(2)]
         normalize_dst_ports_def normalize_ports_step_def
    have normalized_result2: "\<forall>m \<in> get_match ` set (normalize_rules normalize_dst_ports (normalize_rules normalize_src_ports rs)).
            normalized_nnf_match m" by presburger
    from normalize_rules_primitive_extract_preserves_nnf_normalized[OF this wf_disc_sel_common_primitive(3)]
         normalize_src_ips_def
    have normalized_result3: "\<forall>m \<in> get_match ` set (normalize_rules normalize_src_ips (normalize_rules normalize_dst_ports (normalize_rules normalize_src_ports rs))).
            normalized_nnf_match m" by presburger
    from normalize_rules_primitive_extract_preserves_nnf_normalized[OF this wf_disc_sel_common_primitive(4)]
         normalize_dst_ips_def
    have normalized_result4: "\<forall>m \<in> get_match ` set (normalize_rules normalize_dst_ips (normalize_rules normalize_src_ips 
            (normalize_rules normalize_dst_ports (normalize_rules normalize_src_ports rs)))).
              normalized_nnf_match m" by presburger
    thus "\<forall> m \<in> get_match ` set (transform_normalize_primitives rs). normalized_nnf_match m"
      unfolding transform_normalize_primitives_def by simp

    show "?\<gamma>,p\<turnstile> \<langle>transform_normalize_primitives rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> ?\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
     unfolding approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers_t]]
     unfolding approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers]]
     unfolding transform_normalize_primitives_def
     apply(simp)
     apply(subst normalize_rules_match_list_semantics_3)
        using normalize_dst_ips apply simp
       using simplers simple_ruleset_normalize_rules apply blast
      using normalized_result3 apply simp
     apply(subst normalize_rules_match_list_semantics_3)
        using normalize_src_ips apply simp
       using simplers simple_ruleset_normalize_rules apply blast
      using normalized_result2 apply simp
     apply(subst normalize_rules_match_list_semantics_3)
        using normalize_ports_step_Dst apply simp
       using simplers simple_ruleset_normalize_rules apply blast
      using normalized_result1 apply simp
     apply(subst normalize_rules_match_list_semantics_3)
        using normalize_ports_step_Src apply simp
       using simplers simple_ruleset_normalize_rules apply blast
      using normalized apply simp
     by simp


   show  "\<forall> m \<in> get_match ` set rs. normalized_n_primitive disc_sel f m \<Longrightarrow>
          \<forall> m \<in> get_match ` set (transform_normalize_primitives rs). normalized_n_primitive disc_sel f m"
oops








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












(*scratch:*)
fun is_False :: "'a match_expr \<Rightarrow> bool" where
  "is_False (MatchAny) = False" |
  "is_False (Match m) = False" |
  "is_False (MatchAnd m1 m2) = (is_False m1 \<or> is_False m2)" |
  "is_False (MatchNot (MatchAnd m1 m2)) = (is_False (MatchNot m1) \<or> is_False (MatchNot m2))" | (*DeMorgan*)
  "is_False (MatchNot (MatchNot m)) = is_False m" | (*idem*)
  "is_False (MatchNot (MatchAny)) = True" |
  "is_False (MatchNot (Match m)) = False"

lemma "normalized_nnf_match m \<Longrightarrow> normalized_nnf_match (optimize_primitive_univ m) \<or> is_False ((optimize_primitive_univ m))"
  apply(induction m rule: optimize_primitive_univ.induct)
  apply(simp_all)
  apply(safe)
  apply(drule normalized_nnf_match_MatchNot_D)
  apply(simp)
  apply(safe)
  oops

end

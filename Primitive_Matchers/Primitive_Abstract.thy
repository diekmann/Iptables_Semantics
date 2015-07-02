theory Primitive_Abstract
imports
  "../Examples/Firewall_toString"
  "../Primitive_Matchers/Transform"
begin

(*DRAFT*)
(*TODO: die primitive toStrings in eigene thy und diese dann mit weniger dependencies*)

section{*Abstracting over Primitevs*}



text{* Abstract over certain primitives. The first parameter is a function
  @{typ "common_primitive negation_type \<Rightarrow> bool"} to select the primitives to be abstracted over.
  The @{typ common_primitive} is wrapped in a @{typ "common_primitive negation_type"} to let the function
  selectively abstract only over negated, non-negated, or both kinds of primitives.
  This functions requires a @{const normalized_nnf_match}.
*}
fun abstract_primitive :: "(common_primitive negation_type \<Rightarrow> bool) \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
  "abstract_primitive _     MatchAny = MatchAny" |
  "abstract_primitive disc (Match a) = (if disc (Pos a) then Match (Extra (common_primitive_toString a)) else (Match a))" |
  "abstract_primitive disc (MatchNot (Match a)) = (if disc (Neg a) then Match (Extra (''! ''@common_primitive_toString a)) else (MatchNot (Match a)))" |
  "abstract_primitive disc (MatchNot m) = MatchNot (abstract_primitive disc m)" |
  "abstract_primitive disc (MatchAnd m1 m2) = MatchAnd (abstract_primitive disc m1) (abstract_primitive disc m2)"

text{*For example, a simple firewall requires that no negated interfaces and protocols occur in the 
      expression. *}
definition abstract_for_simple_firewall :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr"
  where "abstract_for_simple_firewall \<equiv> abstract_primitive (\<lambda>r. case r of Pos _ \<Rightarrow> False | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_Prot a)"


lemma abstract_primitive_in_doubt_allow_Allow: 
  "normalized_nnf_match m \<Longrightarrow> 
    matches (common_matcher, in_doubt_allow) m action.Accept p \<Longrightarrow>
    matches (common_matcher, in_doubt_allow) (abstract_primitive disc m) action.Accept p"
   by(induction disc m rule: abstract_primitive.induct)
     (simp_all add: bunch_of_lemmata_about_matches)

lemma abstract_primitive_in_doubt_allow_Allow2: 
  "normalized_nnf_match m \<Longrightarrow> 
    \<not> matches (common_matcher, in_doubt_allow) m action.Drop p \<Longrightarrow>
    \<not> matches (common_matcher, in_doubt_allow) (abstract_primitive disc m) action.Drop p"
   apply(induction disc m rule: abstract_primitive.induct)
         apply (simp_all add: bunch_of_lemmata_about_matches)
   apply(auto simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps  split: ternaryvalue.split)
   done



(*TODO: rename*)
lemma abstract_primitive_help1: assumes n: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m" and simple: "simple_ruleset rs"
      and prem: "approximating_bigstep_fun (common_matcher, in_doubt_allow) p rs Undecided = Decision FinalAllow"
      shows "approximating_bigstep_fun (common_matcher, in_doubt_allow) p (optimize_matches (abstract_primitive disc) rs) Undecided = Decision FinalAllow"
  proof -
    let ?\<gamma>="(common_matcher, in_doubt_allow) :: (common_primitive \<Rightarrow> simple_packet \<Rightarrow> ternaryvalue) \<times> (action \<Rightarrow> simple_packet \<Rightarrow> bool)"
      --{*type signature is needed, otherwise @{const in_doubt_allow} would be for arbitrary packet*}

    from simple have "wf_ruleset ?\<gamma> p rs" using good_imp_wf_ruleset simple_imp_good_ruleset by fast
    from this simple prem n show ?thesis
      proof(induction ?\<gamma> p rs Undecided rule: approximating_bigstep_fun_induct_wf)
      case (MatchAccept p m a rs)
        from MatchAccept.prems abstract_primitive_in_doubt_allow_Allow MatchAccept.hyps have
          "matches ?\<gamma> (abstract_primitive disc m) action.Accept p" by simp
        thus ?case by(simp add: optimize_matches_def MatchAccept.hyps)
      next
      case (Nomatch p m a rs) thus ?case
        proof(cases "matches ?\<gamma> (abstract_primitive disc m) a p")
          case False with Nomatch show ?thesis
            apply(simp add: optimize_matches_def)
            using simple_ruleset_tail by blast
          next
          case True
            from Nomatch.prems simple_ruleset_def have "a = action.Accept \<or> a = action.Drop" by force
            from Nomatch.hyps(1) Nomatch.prems(3) abstract_primitive_in_doubt_allow_Allow2 have
              "a = action.Drop \<Longrightarrow> \<not> matches ?\<gamma> (abstract_primitive disc m) action.Drop p" by simp
            with True `a = action.Accept \<or> a = action.Drop` have "a = action.Accept" by blast
            with True show ?thesis by(simp add: optimize_matches_def)
          qed
      qed(simp_all add: simple_ruleset_def)
qed


lemma abstract_primitive_in_doubt_allow_Deny: 
  "normalized_nnf_match m \<Longrightarrow>
    matches (common_matcher, in_doubt_allow) (abstract_primitive disc m) action.Drop p \<Longrightarrow>
    matches (common_matcher, in_doubt_allow) m action.Drop p"
   apply(induction disc m rule: abstract_primitive.induct)
         apply(simp_all add: bunch_of_lemmata_about_matches)
   apply(auto simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps  split: split_if_asm ternaryvalue.split_asm ternaryvalue.split)
   done

lemma abstract_primitive_in_doubt_allow_Deny2: 
  "normalized_nnf_match m \<Longrightarrow> 
    \<not> matches (common_matcher, in_doubt_allow) (abstract_primitive disc m) action.Accept p \<Longrightarrow>
    \<not> matches (common_matcher, in_doubt_allow) m action.Accept p"
   apply(induction disc m rule: abstract_primitive.induct)
         apply (simp_all add: bunch_of_lemmata_about_matches)
    apply(auto simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps  split: split_if_asm ternaryvalue.split_asm ternaryvalue.split)
   done


(*TODO: rename*)
lemma abstract_primitive_in_doubt_allow_help2: assumes n: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m" and simple: "simple_ruleset rs"
      and prem: "approximating_bigstep_fun (common_matcher, in_doubt_allow) p (optimize_matches (abstract_primitive disc) rs) Undecided = Decision FinalDeny"
      shows "approximating_bigstep_fun (common_matcher, in_doubt_allow) p rs Undecided = Decision FinalDeny"
  proof -
    let ?\<gamma>="(common_matcher, in_doubt_allow) :: (common_primitive \<Rightarrow> simple_packet \<Rightarrow> ternaryvalue) \<times> (action \<Rightarrow> simple_packet \<Rightarrow> bool)"
      --{*type signature is needed, otherwise @{const in_doubt_allow} would be for arbitrary packet*}

    from simple have "wf_ruleset ?\<gamma> p rs" using good_imp_wf_ruleset simple_imp_good_ruleset by fast
    from this simple prem n show ?thesis
      proof(induction ?\<gamma> p rs Undecided rule: approximating_bigstep_fun_induct_wf)
      case Empty thus ?case by(simp add: optimize_matches_def)
      next
      case (MatchAccept p m a rs)
        from MatchAccept.prems abstract_primitive_in_doubt_allow_Allow MatchAccept.hyps have
          1: "matches ?\<gamma> (abstract_primitive disc m) action.Accept p" by simp
        from MatchAccept have "approximating_bigstep_fun ?\<gamma> p
          (Rule (abstract_primitive disc m) action.Accept # (optimize_matches (abstract_primitive disc) rs)) Undecided = Decision FinalDeny"
          by(simp add: optimize_matches_def)
        with 1 have False by(simp)
        thus ?case ..
      next
      case (Nomatch p m a rs) thus ?case
        proof(cases "matches ?\<gamma> (abstract_primitive disc m) a p")
          case False with Nomatch show ?thesis
            apply(simp add: optimize_matches_def)
            using simple_ruleset_tail by blast
          next
          case True
            from Nomatch.prems(2) have 1: "approximating_bigstep_fun ?\<gamma> p
              (Rule (abstract_primitive disc m) a # (optimize_matches (abstract_primitive disc) rs)) Undecided = Decision FinalDeny"
              by(simp add: optimize_matches_def)
            from Nomatch.prems simple_ruleset_def have "a = action.Accept \<or> a = action.Drop" by force
            from Nomatch.hyps(1) Nomatch.prems(3) abstract_primitive_in_doubt_allow_Allow2 have
              "a = action.Drop \<Longrightarrow> \<not> matches ?\<gamma> (abstract_primitive disc m) action.Drop p" by simp
            with True `a = action.Accept \<or> a = action.Drop` have "a = action.Accept" by blast
            with 1 True have False by simp
            thus ?thesis ..
          qed
      qed(simp_all add: simple_ruleset_def)
qed


theorem abstract_primitive_in_doubt_allow:
  assumes n: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m" and simple: "simple_ruleset rs"
  defines "\<gamma> \<equiv> (common_matcher, in_doubt_allow)" and "abstract disc \<equiv> optimize_matches (abstract_primitive disc)"
  shows   "{p. \<gamma>,p\<turnstile> \<langle>abstract disc rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny} \<subseteq> {p. \<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny}"
              (is ?deny)
    and   "{p. \<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow} \<subseteq> {p. \<gamma>,p\<turnstile> \<langle>abstract disc rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow}"
              (is ?allow)
  proof -
    from simple have "good_ruleset rs" using simple_imp_good_ruleset by fast
    from optimize_matches_simple_ruleset simple simple_imp_good_ruleset have
      "good_ruleset (optimize_matches (abstract_primitive disc) rs)" by fast
    with approximating_semantics_iff_fun_good_ruleset abstract_primitive_help1[OF n simple] `good_ruleset rs` show ?allow
      unfolding \<gamma>_def abstract_def by fast
    from optimize_matches_simple_ruleset simple simple_imp_good_ruleset have
      "good_ruleset (optimize_matches (abstract_primitive disc) rs)" by fast
    with approximating_semantics_iff_fun_good_ruleset abstract_primitive_in_doubt_allow_help2[OF n simple] `good_ruleset rs` \<gamma>_def show ?deny 
      unfolding \<gamma>_def abstract_def by fast
  qed






(*TODO: in_doubt_deny closure property*)
lemma abstract_primitive_in_doubt_deny_Deny:
  "normalized_nnf_match m \<Longrightarrow> 
    matches (common_matcher, in_doubt_deny) m action.Drop p \<Longrightarrow>
    matches (common_matcher, in_doubt_deny) (abstract_primitive disc m) action.Drop p"
   by(induction disc m rule: abstract_primitive.induct)
     (simp_all add: bunch_of_lemmata_about_matches)

lemma abstract_primitive_in_doubt_deny_Deny2:
  "normalized_nnf_match m \<Longrightarrow> 
    \<not> matches (common_matcher, in_doubt_deny) m action.Accept p \<Longrightarrow>
    \<not> matches (common_matcher, in_doubt_deny) (abstract_primitive disc m) action.Accept p"
   apply(induction disc m rule: abstract_primitive.induct)
                 apply (simp_all add: bunch_of_lemmata_about_matches)
   apply(auto simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps  split: ternaryvalue.split)
   done


(*TODO: rename*)
lemma abstract_primitive_in_doubt_deny_help1: assumes n: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m" and simple: "simple_ruleset rs"
      and prem: "approximating_bigstep_fun (common_matcher, in_doubt_deny) p rs Undecided = Decision FinalDeny"
      shows "approximating_bigstep_fun (common_matcher, in_doubt_deny) p (optimize_matches (abstract_primitive disc) rs) Undecided = Decision FinalDeny"
  proof -
    let ?\<gamma>="(common_matcher, in_doubt_deny) :: (common_primitive \<Rightarrow> simple_packet \<Rightarrow> ternaryvalue) \<times> (action \<Rightarrow> simple_packet \<Rightarrow> bool)"
      --{*type signature is needed, otherwise @{const in_doubt_allow} would be for arbitrary packet*}

    from simple have "wf_ruleset ?\<gamma> p rs" using good_imp_wf_ruleset simple_imp_good_ruleset by fast
    from this simple prem n show ?thesis
      proof(induction ?\<gamma> p rs Undecided rule: approximating_bigstep_fun_induct_wf)
      case (MatchDrop p m a rs)
        from MatchDrop.prems abstract_primitive_in_doubt_deny_Deny MatchDrop.hyps have
          "matches ?\<gamma> (abstract_primitive disc m) action.Drop p" by simp
        thus ?case by(simp add: optimize_matches_def MatchDrop.hyps)
      next
      case (Nomatch p m a rs) thus ?case
        proof(cases "matches ?\<gamma> (abstract_primitive disc m) a p")
          case False with Nomatch show ?thesis
            apply(simp add: optimize_matches_def)
            using simple_ruleset_tail by blast
          next
          case True
            from Nomatch.prems simple_ruleset_def have "a = action.Accept \<or> a = action.Drop" by force
            from Nomatch.hyps(1) Nomatch.prems(3) abstract_primitive_in_doubt_deny_Deny2 have
              "a = action.Accept \<Longrightarrow> \<not> matches ?\<gamma> (abstract_primitive disc m) action.Accept p" by(simp)
            with True `a = action.Accept \<or> a = action.Drop` have "a = action.Drop" by blast
            with True show ?thesis by(simp add: optimize_matches_def)
          qed
      qed(simp_all add: simple_ruleset_def)
qed



lemma abstract_primitive_in_doubt_deny_Allow: 
  "normalized_nnf_match m \<Longrightarrow>
    matches (common_matcher, in_doubt_deny) (abstract_primitive disc m) action.Accept p \<Longrightarrow>
    matches (common_matcher, in_doubt_deny) m action.Accept p"
   apply(induction disc m rule: abstract_primitive.induct)
         apply(simp_all add: bunch_of_lemmata_about_matches)
   apply(auto simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps  split: split_if_asm ternaryvalue.split_asm ternaryvalue.split)
   done

lemma abstract_primitive_in_doubt_deny_Allow2: 
  "normalized_nnf_match m \<Longrightarrow> 
    \<not> matches (common_matcher, in_doubt_deny) (abstract_primitive disc m) action.Drop p \<Longrightarrow>
    \<not> matches (common_matcher, in_doubt_deny) m action.Drop p"
   apply(induction disc m rule: abstract_primitive.induct)
         apply (simp_all add: bunch_of_lemmata_about_matches)
    apply(auto simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps  split: split_if_asm ternaryvalue.split_asm ternaryvalue.split)
   done


(*TODO: rename*)
lemma abstract_primitive_in_doubt_deny_help2: assumes n: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m" and simple: "simple_ruleset rs"
      and prem: "approximating_bigstep_fun (common_matcher, in_doubt_deny) p (optimize_matches (abstract_primitive disc) rs) Undecided = Decision FinalAllow"
      shows "approximating_bigstep_fun (common_matcher, in_doubt_deny) p rs Undecided = Decision FinalAllow"
  proof -
    let ?\<gamma>="(common_matcher, in_doubt_deny) :: (common_primitive \<Rightarrow> simple_packet \<Rightarrow> ternaryvalue) \<times> (action \<Rightarrow> simple_packet \<Rightarrow> bool)"
      --{*type signature is needed, otherwise @{const in_doubt_deny} would be for arbitrary packet*}

    from simple have "wf_ruleset ?\<gamma> p rs" using good_imp_wf_ruleset simple_imp_good_ruleset by fast
    from this simple prem n show ?thesis
      proof(induction ?\<gamma> p rs Undecided rule: approximating_bigstep_fun_induct_wf)
      case Empty thus ?case by(simp add: optimize_matches_def)
      next
      case (MatchAccept p m a rs) thus ?case by auto
      next
      case (MatchDrop p m a rs)
        from MatchDrop.prems abstract_primitive_in_doubt_deny_Deny MatchDrop.hyps have
          1: "matches ?\<gamma> (abstract_primitive disc m) action.Drop p" by simp
        from MatchDrop have "approximating_bigstep_fun ?\<gamma> p
          (Rule (abstract_primitive disc m) action.Drop # (optimize_matches (abstract_primitive disc) rs)) Undecided = Decision FinalAllow"
          by(simp add: optimize_matches_def)
        with 1 have False by(simp)
        thus ?case ..
      next
      case (Nomatch p m a rs) thus ?case
        proof(cases "matches ?\<gamma> (abstract_primitive disc m) a p")
          case False with Nomatch show ?thesis
            apply(simp add: optimize_matches_def)
            using simple_ruleset_tail by blast
          next
          case True
            from Nomatch.prems(2) have 1: "approximating_bigstep_fun ?\<gamma> p
              (Rule (abstract_primitive disc m) a # (optimize_matches (abstract_primitive disc) rs)) Undecided = Decision FinalAllow"
              by(simp add: optimize_matches_def)
            from Nomatch.prems simple_ruleset_def have "a = action.Accept \<or> a = action.Drop" by force
            from Nomatch.hyps(1) Nomatch.prems(3) abstract_primitive_in_doubt_deny_Deny2 have
              "a = action.Accept \<Longrightarrow> \<not> matches ?\<gamma> (abstract_primitive disc m) action.Accept p" by simp
            with True `a = action.Accept \<or> a = action.Drop` have "a = action.Drop" by blast
            with 1 True have False by force
            thus ?thesis ..
          qed
      qed(simp_all add: simple_ruleset_def)
qed


lemma abstract_primitive_in_doubt_deny:
  assumes n: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m" and simple: "simple_ruleset rs"
  shows   "{p. (common_matcher, in_doubt_deny),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny} \<subseteq>
           {p. (common_matcher, in_doubt_deny),p\<turnstile> \<langle>optimize_matches (abstract_primitive disc) rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny}"
  proof -
    let ?\<gamma>="(common_matcher, in_doubt_allow) :: (common_primitive \<Rightarrow> simple_packet \<Rightarrow> ternaryvalue) \<times> (action \<Rightarrow> simple_packet \<Rightarrow> bool)"
    from simple have "good_ruleset rs" using simple_imp_good_ruleset by fast
    from optimize_matches_simple_ruleset simple simple_imp_good_ruleset have
      "good_ruleset (optimize_matches (abstract_primitive disc) rs)" by fast
    with approximating_semantics_iff_fun_good_ruleset abstract_primitive_in_doubt_deny_help1[OF n simple] `good_ruleset rs` show ?thesis by fast
  qed


end
theory Primitive_Abstract
imports
  Common_Primitive_toString
  Transform
  Conntrack_State_Transform
begin

section{*Abstracting over Primitives*}



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
  where "abstract_for_simple_firewall \<equiv> abstract_primitive (\<lambda>r. case r
                of Pos a \<Rightarrow> is_CT_State a \<or> is_L4_Flags a
                |  Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_Prot a \<or> is_CT_State a \<or> is_L4_Flags a)"


lemma abstract_primitive_preserves_normalized:
  "normalized_src_ports m \<Longrightarrow> normalized_src_ports (abstract_primitive disc m)"
  "normalized_dst_ports m \<Longrightarrow> normalized_dst_ports (abstract_primitive disc m)"
  "normalized_src_ips m \<Longrightarrow> normalized_src_ips (abstract_primitive disc m)"
  "normalized_dst_ips m \<Longrightarrow> normalized_dst_ips (abstract_primitive disc m)"
  "normalized_nnf_match m \<Longrightarrow> normalized_nnf_match (abstract_primitive disc m)"
  apply(induction disc m rule: abstract_primitive.induct)
  apply(simp_all)
  done
lemma abstract_primitive_preserves_nodisc:
  "\<not> has_disc disc' m \<Longrightarrow> (\<forall>str. \<not> disc' (Extra str)) \<Longrightarrow> \<not> has_disc disc' (abstract_primitive disc m)"
  apply(induction disc m rule: abstract_primitive.induct)
  apply(simp_all)
  done



text{*The function @{const ctstate_assume_state} can be used to fix a state and hence remove all state matches from the ruleset.
      It is therefore advisable to create a simple firewall for a fixed state, e.g. with @{const ctstate_assume_new} before
      calling to @{const abstract_for_simple_firewall}.*}
lemma not_hasdisc_ctstate_assume_state: "\<not> has_disc is_CT_State (ctstate_assume_state s m)"
  by(induction m rule: ctstate_assume_state.induct) (simp_all)


lemma abstract_for_simple_firewall_hasdisc:
  "\<not> has_disc is_CT_State (abstract_for_simple_firewall m)"
  "\<not> has_disc is_L4_Flags (abstract_for_simple_firewall m)"
  unfolding abstract_for_simple_firewall_def
  apply(induction "(\<lambda>r. case r of Pos a \<Rightarrow> is_CT_State a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_Prot a \<or> is_CT_State a)" m rule: abstract_primitive.induct)
  apply(simp_all)
  done

lemma abstract_for_simple_firewall_negated_ifaces_prots:
    "normalized_nnf_match m \<Longrightarrow> \<not> has_disc_negated (\<lambda>a. is_Iiface a \<or> is_Oiface a) False (abstract_for_simple_firewall m)"
    "normalized_nnf_match m \<Longrightarrow> \<not> has_disc_negated is_Prot False (abstract_for_simple_firewall m)"
  unfolding abstract_for_simple_firewall_def
  apply(induction "(\<lambda>r. case r of Pos a \<Rightarrow> is_CT_State a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_Prot a \<or> is_CT_State a)" m rule: abstract_primitive.induct)
  apply(simp_all)
  done


context
begin
  private lemma abstract_primitive_in_doubt_allow_Allow: 
    "prinitive_matcher_generic \<beta> \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> 
      matches (\<beta>, in_doubt_allow) m action.Accept p \<Longrightarrow>
      matches (\<beta>, in_doubt_allow) (abstract_primitive disc m) action.Accept p"
     by(induction disc m rule: abstract_primitive.induct)
       (simp_all add: bunch_of_lemmata_about_matches prinitive_matcher_generic_def)
  
  private lemma abstract_primitive_in_doubt_allow_Allow2: 
    "prinitive_matcher_generic \<beta> \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> 
      \<not> matches (\<beta>, in_doubt_allow) m action.Drop p \<Longrightarrow>
      \<not> matches (\<beta>, in_doubt_allow) (abstract_primitive disc m) action.Drop p"
     proof(induction disc m rule: abstract_primitive.induct)
     case(5 m1 m2) thus ?case
           apply (simp add: bunch_of_lemmata_about_matches)
           apply(auto simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps  split: ternaryvalue.split)
           done
     qed(simp_all add: bunch_of_lemmata_about_matches prinitive_matcher_generic_def)
  


  private lemma abstract_primitive_help1:
    assumes generic: "prinitive_matcher_generic \<beta>"
        and n: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m"
        and simple: "simple_ruleset rs"
        and prem: "approximating_bigstep_fun (\<beta>, in_doubt_allow) p rs Undecided = Decision FinalAllow"
      shows "approximating_bigstep_fun (\<beta>, in_doubt_allow) p (optimize_matches (abstract_primitive disc) rs) Undecided = Decision FinalAllow"
    proof -
      let ?\<gamma>="(\<beta>, in_doubt_allow) :: (common_primitive \<Rightarrow> simple_packet \<Rightarrow> ternaryvalue) \<times> (action \<Rightarrow> simple_packet \<Rightarrow> bool)"
        --{*type signature is needed, otherwise @{const in_doubt_allow} would be for arbitrary packet*}
  
      from simple have "wf_ruleset ?\<gamma> p rs" using good_imp_wf_ruleset simple_imp_good_ruleset by fast
      from this simple prem n show ?thesis
        proof(induction ?\<gamma> p rs Undecided rule: approximating_bigstep_fun_induct_wf)
        case (MatchAccept p m a rs)
          from MatchAccept.prems
            abstract_primitive_in_doubt_allow_Allow[OF generic] MatchAccept.hyps have
            "matches ?\<gamma> (abstract_primitive disc m) action.Accept p" by simp
          thus ?case
          apply(simp add: MatchAccept.hyps(2))
          using optimize_matches_matches_fst by fastforce 
        next
        case (Nomatch p m a rs) thus ?case
          proof(cases "matches ?\<gamma> (abstract_primitive disc m) a p")
            case False with Nomatch show ?thesis
              apply(simp add: optimize_matches_def)
              using simple_ruleset_tail by blast
            next
            case True
              from Nomatch.prems simple_ruleset_def have "a = action.Accept \<or> a = action.Drop" by force
              from Nomatch.hyps(1) Nomatch.prems(3) abstract_primitive_in_doubt_allow_Allow2[OF generic] have
                "a = action.Drop \<Longrightarrow> \<not> matches ?\<gamma> (abstract_primitive disc m) action.Drop p" by simp
              with True `a = action.Accept \<or> a = action.Drop` have "a = action.Accept" by blast
              with True show ?thesis
                using optimize_matches_matches_fst by fastforce 
            qed
        qed(simp_all add: simple_ruleset_def)
  qed

  private lemma abstract_primitive_in_doubt_allow_Deny: 
    "prinitive_matcher_generic \<beta> \<Longrightarrow> normalized_nnf_match m \<Longrightarrow>
      matches (\<beta>, in_doubt_allow) (abstract_primitive disc m) action.Drop p \<Longrightarrow>
      matches (\<beta>, in_doubt_allow) m action.Drop p"
     apply(induction disc m rule: abstract_primitive.induct)
           apply(simp_all add: bunch_of_lemmata_about_matches prinitive_matcher_generic_def)
      apply(auto simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps 
        split: split_if_asm ternaryvalue.split_asm)
     done
  
  private lemma abstract_primitive_in_doubt_allow_Deny2: 
    "prinitive_matcher_generic \<beta> \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> 
      \<not> matches (\<beta>, in_doubt_allow) (abstract_primitive disc m) action.Accept p \<Longrightarrow>
      \<not> matches (\<beta>, in_doubt_allow) m action.Accept p"
     apply(induction disc m rule: abstract_primitive.induct)
           apply (simp_all add: bunch_of_lemmata_about_matches prinitive_matcher_generic_def)
      apply(auto simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps 
        split: split_if_asm ternaryvalue.split_asm)
     done
  
  private lemma abstract_primitive_in_doubt_allow_help2:
    assumes generic: "prinitive_matcher_generic \<beta>"
        and n: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m" and simple: "simple_ruleset rs"
        and prem: "approximating_bigstep_fun (\<beta>, in_doubt_allow) p (optimize_matches (abstract_primitive disc) rs) Undecided = Decision FinalDeny"
        shows "approximating_bigstep_fun (\<beta>, in_doubt_allow) p rs Undecided = Decision FinalDeny"
    proof -
      let ?\<gamma>="(\<beta>, in_doubt_allow) :: (common_primitive \<Rightarrow> simple_packet \<Rightarrow> ternaryvalue) \<times> (action \<Rightarrow> simple_packet \<Rightarrow> bool)"
        --{*type signature is needed, otherwise @{const in_doubt_allow} would be for arbitrary packet*}
  
      from simple have "wf_ruleset ?\<gamma> p rs" using good_imp_wf_ruleset simple_imp_good_ruleset by fast
      from this simple prem n show ?thesis
        proof(induction ?\<gamma> p rs Undecided rule: approximating_bigstep_fun_induct_wf)
        case Empty thus ?case by(simp add: optimize_matches_def)
        next
        case (MatchAccept p m a rs)
          from MatchAccept.prems abstract_primitive_in_doubt_allow_Allow[OF generic] MatchAccept.hyps have
            1: "matches ?\<gamma> (abstract_primitive disc m) action.Accept p" by simp
          with MatchAccept have "approximating_bigstep_fun ?\<gamma> p
            (Rule (abstract_primitive disc m) action.Accept # (optimize_matches (abstract_primitive disc) rs)) Undecided = Decision FinalDeny"
            using optimize_matches_matches_fst by metis
          with 1 have False by(simp)
          thus ?case ..
        next
        case (Nomatch p m a rs) thus ?case
          proof(cases "matches ?\<gamma> (abstract_primitive disc m) a p")
            case False
            with Nomatch show ?thesis
              apply(simp add: optimize_matches_def)
              (*sledgehammer*) (*TODO*)
              proof -
                assume a1: "\<lbrakk>simple_ruleset rs; approximating_bigstep_fun (\<beta>, in_doubt_allow) p (optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs) Undecided = Decision FinalDeny\<rbrakk> \<Longrightarrow> approximating_bigstep_fun (\<beta>, in_doubt_allow) p rs Undecided = Decision FinalDeny"
                assume a2: "simple_ruleset (Rule m a # rs)"
                assume a3: "\<not> matches (\<beta>, in_doubt_allow) (abstract_primitive disc m) a p"
                assume a4: "approximating_bigstep_fun (\<beta>, in_doubt_allow) p (case if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m) of None \<Rightarrow> optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs | Some m \<Rightarrow> Rule m a # optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs) Undecided = Decision FinalDeny"
                have f5: "approximating_bigstep_fun (\<beta>, in_doubt_allow) p (Rule (abstract_primitive disc m) a # optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs) Undecided = approximating_bigstep_fun (\<beta>, in_doubt_allow) p (optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs) Undecided"
                  using a3 by simp
                have f6: "Rule (abstract_primitive disc m) a # optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs = (case Some (abstract_primitive disc m) of None \<Rightarrow> optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs | Some m \<Rightarrow> Rule m a # optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs)"
                  by simp
                have f7: "simple_ruleset rs"
                  using a2 simple_ruleset_tail by blast
                have f8: "None = (if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) \<longrightarrow> approximating_bigstep_fun (\<beta>, in_doubt_allow) p (optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs) Undecided = Decision FinalDeny"
                  using a4 by force
                { assume "approximating_bigstep_fun (\<beta>, in_doubt_allow) p (optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs) Undecided \<noteq> Decision FinalDeny"
                  hence "Rule (abstract_primitive disc m) a # optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs \<noteq> (case if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m) of None \<Rightarrow> optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs | Some m \<Rightarrow> Rule m a # optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs)"
                    using f5 a4 by force
                  hence "simple_ruleset rs \<and> approximating_bigstep_fun (\<beta>, in_doubt_allow) p (optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs) Undecided = Decision FinalDeny"
                    using f8 f7 f6 by presburger }
                thus "approximating_bigstep_fun (\<beta>, in_doubt_allow) p rs Undecided = Decision FinalDeny"
                  using a2 a1 simple_ruleset_tail by blast
              qed
            next
            case True
              from Nomatch.prems(2) True have 1: "approximating_bigstep_fun ?\<gamma> p
                (Rule (abstract_primitive disc m) a # (optimize_matches (abstract_primitive disc) rs)) Undecided = Decision FinalDeny"
                using optimize_matches_matches_fst by metis
                
              from Nomatch.prems simple_ruleset_def have "a = action.Accept \<or> a = action.Drop" by force
              from Nomatch.hyps(1) Nomatch.prems(3) abstract_primitive_in_doubt_allow_Allow2[OF generic] have
                "a = action.Drop \<Longrightarrow> \<not> matches ?\<gamma> (abstract_primitive disc m) action.Drop p" by simp
              with True `a = action.Accept \<or> a = action.Drop` have "a = action.Accept" by blast
              with 1 True have False by simp
              thus ?thesis ..
            qed
        qed(simp_all add: simple_ruleset_def)
  qed
  
  
  theorem abstract_primitive_in_doubt_allow_generic:
    assumes generic: "prinitive_matcher_generic \<beta>"
       and n: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m" and simple: "simple_ruleset rs"
    defines "\<gamma> \<equiv> (\<beta>, in_doubt_allow)" and "abstract disc \<equiv> optimize_matches (abstract_primitive disc)"
    shows   "{p. \<gamma>,p\<turnstile> \<langle>abstract disc rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny} \<subseteq> {p. \<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny}"
                (is ?deny)
      and   "{p. \<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow} \<subseteq> {p. \<gamma>,p\<turnstile> \<langle>abstract disc rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow}"
                (is ?allow)
    proof -
      from simple have "good_ruleset rs" using simple_imp_good_ruleset by fast
      from optimize_matches_simple_ruleset simple simple_imp_good_ruleset have
       good:  "good_ruleset (optimize_matches (abstract_primitive disc) rs)" by fast
      with approximating_semantics_iff_fun_good_ruleset abstract_primitive_help1[OF generic n simple] `good_ruleset rs` show ?allow
        unfolding \<gamma>_def abstract_def by fast
      from good approximating_semantics_iff_fun_good_ruleset abstract_primitive_in_doubt_allow_help2[OF generic n simple] `good_ruleset rs` \<gamma>_def show ?deny 
        unfolding \<gamma>_def abstract_def by fast
    qed
  corollary abstract_primitive_in_doubt_allow:
    assumes generic: "prinitive_matcher_generic \<beta>"
       and n: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m" and simple: "simple_ruleset rs"
    defines "\<gamma> \<equiv> (common_matcher, in_doubt_allow)" and "abstract disc \<equiv> optimize_matches (abstract_primitive disc)"
    shows   "{p. \<gamma>,p\<turnstile> \<langle>abstract disc rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny} \<subseteq> {p. \<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny}"
      and   "{p. \<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow} \<subseteq> {p. \<gamma>,p\<turnstile> \<langle>abstract disc rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow}"
    unfolding \<gamma>_def abstract_def
    using assms abstract_primitive_in_doubt_allow_generic[OF prinitive_matcher_generic_common_matcher] by simp_all
end


context
begin
  private lemma abstract_primitive_in_doubt_deny_Deny:
    "normalized_nnf_match m \<Longrightarrow> 
      matches (common_matcher, in_doubt_deny) m action.Drop p \<Longrightarrow>
      matches (common_matcher, in_doubt_deny) (abstract_primitive disc m) action.Drop p"
     by(induction disc m rule: abstract_primitive.induct)
       (simp_all add: bunch_of_lemmata_about_matches)
  
  private lemma abstract_primitive_in_doubt_deny_Deny2:
    "normalized_nnf_match m \<Longrightarrow> 
      \<not> matches (common_matcher, in_doubt_deny) m action.Accept p \<Longrightarrow>
      \<not> matches (common_matcher, in_doubt_deny) (abstract_primitive disc m) action.Accept p"
     apply(induction disc m rule: abstract_primitive.induct)
                   apply (simp_all add: bunch_of_lemmata_about_matches)
     apply(auto simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps  split: ternaryvalue.split)
     done
  
  
  private lemma abstract_primitive_in_doubt_deny_help1: assumes n: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m" and simple: "simple_ruleset rs"
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
          thus ?case 
          apply(simp add: MatchDrop.hyps(2))
          using optimize_matches_matches_fst by fastforce
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
              with True show ?thesis using optimize_matches_matches_fst by fastforce
            qed
        qed(simp_all add: simple_ruleset_def)
  qed
  
  
  
  private lemma abstract_primitive_in_doubt_deny_Allow: 
    "normalized_nnf_match m \<Longrightarrow>
      matches (common_matcher, in_doubt_deny) (abstract_primitive disc m) action.Accept p \<Longrightarrow>
      matches (common_matcher, in_doubt_deny) m action.Accept p"
     apply(induction disc m rule: abstract_primitive.induct)
           apply(simp_all add: bunch_of_lemmata_about_matches)
      apply(auto simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps  split: split_if_asm ternaryvalue.split_asm ternaryvalue.split)
     done
  
  private lemma abstract_primitive_in_doubt_deny_Allow2: 
    "normalized_nnf_match m \<Longrightarrow> 
      \<not> matches (common_matcher, in_doubt_deny) (abstract_primitive disc m) action.Drop p \<Longrightarrow>
      \<not> matches (common_matcher, in_doubt_deny) m action.Drop p"
     apply(induction disc m rule: abstract_primitive.induct)
           apply (simp_all add: bunch_of_lemmata_about_matches)
       apply(auto simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps  split: split_if_asm ternaryvalue.split_asm ternaryvalue.split)
     done
  
  
  private lemma abstract_primitive_in_doubt_deny_help2: assumes n: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m" and simple: "simple_ruleset rs"
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
          using optimize_matches_matches_fst 1 by fastforce
          with 1 have False by(simp)
          thus ?case ..
        next
        case (Nomatch p m a rs) thus ?case
          proof(cases "matches ?\<gamma> (abstract_primitive disc m) a p")
            case False with Nomatch show ?thesis
              apply(simp add: optimize_matches_def)
              (*TODO sledgehammer and a copy from above*)
              proof -
                assume a1: "\<lbrakk>simple_ruleset rs; approximating_bigstep_fun (common_matcher, in_doubt_deny) p (optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs) Undecided = Decision FinalAllow\<rbrakk> \<Longrightarrow> approximating_bigstep_fun (common_matcher, in_doubt_deny) p rs Undecided = Decision FinalAllow"
                assume a2: "simple_ruleset (Rule m a # rs)"
                assume a3: "\<not> matches (common_matcher, in_doubt_deny) (abstract_primitive disc m) a p"
                assume a4: "approximating_bigstep_fun (common_matcher, in_doubt_deny) p (case if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m) of None \<Rightarrow> optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs | Some m \<Rightarrow> Rule m a # optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs) Undecided = Decision FinalAllow"
                have f5: "approximating_bigstep_fun (common_matcher, in_doubt_deny) p (Rule (abstract_primitive disc m) a # optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs) Undecided = approximating_bigstep_fun (common_matcher, in_doubt_deny) p (optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs) Undecided"
                  using a3 by simp
                have f6: "Rule (abstract_primitive disc m) a # optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs = (case Some (abstract_primitive disc m) of None \<Rightarrow> optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs | Some m \<Rightarrow> Rule m a # optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs)"
                  by simp
                have f7: "simple_ruleset rs"
                  using a2 simple_ruleset_tail by blast
                have f8: "None = (if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) \<longrightarrow> approximating_bigstep_fun (common_matcher, in_doubt_deny) p (optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs) Undecided = Decision FinalAllow"
                  using a4 by force
                { assume "approximating_bigstep_fun (common_matcher, in_doubt_deny) p (optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs) Undecided \<noteq> Decision FinalAllow"
                  hence "Rule (abstract_primitive disc m) a # optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs \<noteq> (case if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m) of None \<Rightarrow> optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs | Some m \<Rightarrow> Rule m a # optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs)"
                    using f5 a4 by force
                  hence "simple_ruleset rs \<and> approximating_bigstep_fun (common_matcher, in_doubt_deny) p (optimize_matches_option (\<lambda>m. if matcheq_matchNone (abstract_primitive disc m) then None else Some (abstract_primitive disc m)) rs) Undecided = Decision FinalAllow"
                    using f8 f7 f6 by presburger }
                thus "approximating_bigstep_fun (common_matcher, in_doubt_deny) p rs Undecided = Decision FinalAllow"
                  using a2 a1 simple_ruleset_tail by blast
              qed
            next
            case True
              from Nomatch.prems(2) True have 1: "approximating_bigstep_fun ?\<gamma> p
                (Rule (abstract_primitive disc m) a # (optimize_matches (abstract_primitive disc) rs)) Undecided = Decision FinalAllow"
                using optimize_matches_matches_fst by metis
              from Nomatch.prems simple_ruleset_def have "a = action.Accept \<or> a = action.Drop" by force
              from Nomatch.hyps(1) Nomatch.prems(3) abstract_primitive_in_doubt_deny_Deny2 have
                "a = action.Accept \<Longrightarrow> \<not> matches ?\<gamma> (abstract_primitive disc m) action.Accept p" by simp
              with True `a = action.Accept \<or> a = action.Drop` have "a = action.Drop" by blast
              with 1 True have False by force
              thus ?thesis ..
            qed
        qed(simp_all add: simple_ruleset_def)
  qed
  
  
  theorem abstract_primitive_in_doubt_deny:
    assumes n: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m" and simple: "simple_ruleset rs"
    defines "\<gamma> \<equiv> (common_matcher, in_doubt_deny)" and "abstract disc \<equiv> optimize_matches (abstract_primitive disc)"
    shows   "{p. \<gamma>,p\<turnstile> \<langle>abstract disc rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow} \<subseteq> {p. \<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow}"
             (is ?allow)
    and     "{p. \<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny} \<subseteq> {p. \<gamma>,p\<turnstile> \<langle>abstract disc rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny}"
             (is ?deny)
    proof -
      from simple have "good_ruleset rs" using simple_imp_good_ruleset by fast
      from optimize_matches_simple_ruleset simple simple_imp_good_ruleset have
        good: "good_ruleset (optimize_matches (abstract_primitive disc) rs)" by fast
      with approximating_semantics_iff_fun_good_ruleset abstract_primitive_in_doubt_deny_help1[OF n simple] `good_ruleset rs` show ?deny
        unfolding \<gamma>_def abstract_def by fast
      from good approximating_semantics_iff_fun_good_ruleset abstract_primitive_in_doubt_deny_help2[OF n simple] `good_ruleset rs` show ?allow
        unfolding \<gamma>_def abstract_def by fast
    qed
end



end
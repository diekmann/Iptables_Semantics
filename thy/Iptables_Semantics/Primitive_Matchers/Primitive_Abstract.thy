theory Primitive_Abstract
imports
  Common_Primitive_toString
  Transform
  Conntrack_State_Transform
begin

section\<open>Abstracting over Primitives\<close>



text\<open>Abstract over certain primitives. The first parameter is a function
  @{typ "'i::len common_primitive negation_type \<Rightarrow> bool"} to select the primitives to be abstracted over.
  The @{typ "'i::len common_primitive"} is wrapped in a @{typ "'i::len common_primitive negation_type"} to let the function
  selectively abstract only over negated, non-negated, or both kinds of primitives.
  This functions requires a @{const normalized_nnf_match}.
\<close>
(*requires toString function!*)
fun abstract_primitive
  :: "('i::len common_primitive negation_type \<Rightarrow> bool) \<Rightarrow> 'i common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr"
where
  "abstract_primitive _     MatchAny = MatchAny" |
  "abstract_primitive disc (Match a) =
      (if
         disc (Pos a)
       then
         Match (Extra (common_primitive_toString ipaddr_generic_toString a))
       else
         (Match a))" |
  "abstract_primitive disc (MatchNot (Match a)) =
      (if
         disc (Neg a)
       then
         Match (Extra (''! ''@common_primitive_toString ipaddr_generic_toString a))
       else
         (MatchNot (Match a)))" |
  "abstract_primitive disc (MatchNot m) = MatchNot (abstract_primitive disc m)" |
  "abstract_primitive disc (MatchAnd m1 m2) = MatchAnd (abstract_primitive disc m1) (abstract_primitive disc m2)"


text\<open>For example, a simple firewall requires that no negated interfaces and protocols occur in the 
      expression.\<close>
definition abstract_for_simple_firewall :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr"
  where "abstract_for_simple_firewall \<equiv> abstract_primitive (\<lambda>r. case r
                of Pos a \<Rightarrow> is_CT_State a \<or> is_L4_Flags a
                |  Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_Prot a \<or> is_CT_State a \<or> is_L4_Flags a)"


lemma abstract_primitive_preserves_normalized:
  "normalized_src_ports m \<Longrightarrow> normalized_src_ports (abstract_primitive disc m)"
  "normalized_dst_ports m \<Longrightarrow> normalized_dst_ports (abstract_primitive disc m)"
  "normalized_src_ips m \<Longrightarrow> normalized_src_ips (abstract_primitive disc m)"
  "normalized_dst_ips m \<Longrightarrow> normalized_dst_ips (abstract_primitive disc m)"
  "normalized_nnf_match m \<Longrightarrow> normalized_nnf_match (abstract_primitive disc m)"
  by(induction disc m rule: abstract_primitive.induct) (simp_all)
lemma abstract_primitive_preserves_nodisc:
  "\<not> has_disc disc' m \<Longrightarrow> (\<forall>str. \<not> disc' (Extra str)) \<Longrightarrow> \<not> has_disc disc' (abstract_primitive disc m)"
  by(induction disc m rule: abstract_primitive.induct)(simp_all)
lemma abstract_primitive_preserves_nodisc_nedgated:
  "\<not> has_disc_negated disc' neg m \<Longrightarrow> (\<forall>str. \<not> disc' (Extra str)) \<Longrightarrow> \<not> has_disc_negated disc' neg (abstract_primitive disc m)"
  by(induction disc m arbitrary: neg rule: abstract_primitive.induct) simp+

lemma abstract_primitive_nodisc:
  "\<forall>x. disc' x \<longrightarrow> disc (Pos x) \<and> disc (Neg x)  \<Longrightarrow> (\<forall>str. \<not> disc' (Extra str)) \<Longrightarrow> \<not> has_disc disc' (abstract_primitive disc m)"
  by(induction disc m rule: abstract_primitive.induct) auto
  
lemma abstract_primitive_preserves_not_has_disc_negated:
  "\<forall>a. \<not> disc (Extra a)\<Longrightarrow> \<not> has_disc_negated disc neg m \<Longrightarrow> \<not> has_disc_negated disc neg (abstract_primitive sel_f m)"
by(induction sel_f m arbitrary: neg rule: abstract_primitive.induct) simp+

lemma abstract_for_simple_firewall_preserves_nodisc_negated:
  "\<forall>a. \<not> disc (Extra a)\<Longrightarrow> \<not> has_disc_negated disc False m \<Longrightarrow> \<not> has_disc_negated disc False (abstract_for_simple_firewall m)"
unfolding abstract_for_simple_firewall_def
using abstract_primitive_preserves_nodisc_nedgated by blast

text\<open>The function @{const ctstate_assume_state} can be used to fix a state and hence remove all state matches from the ruleset.
      It is therefore advisable to create a simple firewall for a fixed state, e.g. with @{const ctstate_assume_new} before
      calling to @{const abstract_for_simple_firewall}.\<close>
lemma not_hasdisc_ctstate_assume_state: "\<not> has_disc is_CT_State (ctstate_assume_state s m)"
  by(induction m rule: ctstate_assume_state.induct) (simp_all)


lemma abstract_for_simple_firewall_hasdisc: fixes m :: "'i::len common_primitive match_expr"
  shows "\<not> has_disc is_CT_State (abstract_for_simple_firewall m)"
  and   "\<not> has_disc is_L4_Flags (abstract_for_simple_firewall m)"
  unfolding abstract_for_simple_firewall_def
  apply(induction "(\<lambda>r:: 'i common_primitive negation_type. case r of Pos a \<Rightarrow> is_CT_State a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_Prot a \<or> is_CT_State a)" m rule: abstract_primitive.induct)
  apply(simp_all)
  done

lemma abstract_for_simple_firewall_negated_ifaces_prots: fixes m :: "'i::len common_primitive match_expr"
  shows  "normalized_nnf_match m \<Longrightarrow> \<not> has_disc_negated (\<lambda>a. is_Iiface a \<or> is_Oiface a) False (abstract_for_simple_firewall m)"
  and "normalized_nnf_match m \<Longrightarrow> \<not> has_disc_negated is_Prot False (abstract_for_simple_firewall m)"
  unfolding abstract_for_simple_firewall_def
  apply(induction "(\<lambda>r:: 'i common_primitive negation_type. case r of Pos a \<Rightarrow> is_CT_State a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_Prot a \<or> is_CT_State a)" m rule: abstract_primitive.induct)
  apply(simp_all)
  done


context
begin
  private lemma abstract_primitive_in_doubt_allow_Allow: 
    "primitive_matcher_generic \<beta> \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> 
      matches (\<beta>, in_doubt_allow) m action.Accept p \<Longrightarrow>
      matches (\<beta>, in_doubt_allow) (abstract_primitive disc m) action.Accept p"
     by(induction disc m rule: abstract_primitive.induct)
       (simp_all add: bunch_of_lemmata_about_matches(1) primitive_matcher_generic.Extra_single)
  
  private lemma abstract_primitive_in_doubt_allow_Allow2: 
    "primitive_matcher_generic \<beta> \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> 
      \<not> matches (\<beta>, in_doubt_allow) m action.Drop p \<Longrightarrow>
      \<not> matches (\<beta>, in_doubt_allow) (abstract_primitive disc m) action.Drop p"
     proof(induction disc m rule: abstract_primitive.induct)
     case(5 m1 m2) thus ?case by (auto simp add: bunch_of_lemmata_about_matches(1))
     qed(simp_all add: bunch_of_lemmata_about_matches(1) primitive_matcher_generic.Extra_single)

  private lemma abstract_primitive_in_doubt_allow_Deny: 
    "primitive_matcher_generic \<beta> \<Longrightarrow> normalized_nnf_match m \<Longrightarrow>
      matches (\<beta>, in_doubt_allow) (abstract_primitive disc m) action.Drop p \<Longrightarrow>
      matches (\<beta>, in_doubt_allow) m action.Drop p"
     apply(induction disc m rule: abstract_primitive.induct)
           apply (simp_all add: bunch_of_lemmata_about_matches(1))
       apply(auto simp add: primitive_matcher_generic.Extra_single primitive_matcher_generic.Extra_single_not split: split_if_asm)
     done
  
  private lemma abstract_primitive_in_doubt_allow_Deny2: 
    "primitive_matcher_generic \<beta> \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> 
      \<not> matches (\<beta>, in_doubt_allow) (abstract_primitive disc m) action.Accept p \<Longrightarrow>
      \<not> matches (\<beta>, in_doubt_allow) m action.Accept p"
     apply(induction disc m rule: abstract_primitive.induct)
           apply (simp_all add: bunch_of_lemmata_about_matches(1))
       apply(auto simp add: primitive_matcher_generic.Extra_single primitive_matcher_generic.Extra_single_not split: split_if_asm)
     done
  
  theorem abstract_primitive_in_doubt_allow_generic:
    fixes \<beta>::"('i::len common_primitive, ('i, 'a) tagged_packet_scheme) exact_match_tac"
    assumes generic: "primitive_matcher_generic \<beta>"
       and n: "\<forall> r \<in> set rs. normalized_nnf_match (get_match r)"
       and simple: "simple_ruleset rs"
    defines "\<gamma> \<equiv> (\<beta>, in_doubt_allow)" and "abstract disc \<equiv> optimize_matches (abstract_primitive disc)"
    shows   "{p. \<gamma>,p\<turnstile> \<langle>abstract disc rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny} \<subseteq> {p. \<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny}"
                (is ?deny)
      and   "{p. \<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow} \<subseteq> {p. \<gamma>,p\<turnstile> \<langle>abstract disc rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow}"
                (is ?allow)
    proof -
      from simple have "good_ruleset rs" using simple_imp_good_ruleset by fast
      from optimize_matches_simple_ruleset simple simple_imp_good_ruleset have
       good: "good_ruleset (optimize_matches (abstract_primitive disc) rs)" by fast

      let ?\<gamma>="(\<beta>, in_doubt_allow) :: ('i::len common_primitive, ('i, 'a) tagged_packet_scheme) match_tac"
        --\<open>type signature is needed, otherwise @{const in_doubt_allow} would be for arbitrary packet\<close>

      have abstract_primitive_in_doubt_allow_help1:
        "approximating_bigstep_fun \<gamma> p (optimize_matches (abstract_primitive disc) rs) Undecided = Decision FinalAllow"
        if prem: "approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow" for p
        proof -
          from simple have "wf_ruleset \<gamma> p rs" using good_imp_wf_ruleset simple_imp_good_ruleset by fast
          from this simple prem n show ?thesis
            unfolding \<gamma>_def
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
                  from Nomatch.prems(1) have "a = action.Accept \<or> a = action.Drop" by(simp add: simple_ruleset_def)
                  from Nomatch.hyps(1) Nomatch.prems(3) abstract_primitive_in_doubt_allow_Allow2[OF generic] have
                    "a = action.Drop \<Longrightarrow> \<not> matches ?\<gamma> (abstract_primitive disc m) action.Drop p" by simp
                  with True \<open>a = action.Accept \<or> a = action.Drop\<close> have "a = action.Accept" by blast
                  with True show ?thesis
                    using optimize_matches_matches_fst by fastforce 
                qed
            qed(simp_all add: simple_ruleset_def)
      qed

      have abstract_primitive_in_doubt_allow_help2:
        "approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny"
        if prem: "approximating_bigstep_fun \<gamma> p (optimize_matches (abstract_primitive disc) rs) Undecided = Decision FinalDeny"
        for p
        proof -
          from simple have "wf_ruleset \<gamma> p rs" using good_imp_wf_ruleset simple_imp_good_ruleset by fast
          from this simple prem n show ?thesis
            unfolding \<gamma>_def
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
                with Nomatch.prems(2) have "approximating_bigstep_fun ?\<gamma> p (optimize_matches (abstract_primitive disc) rs) Undecided = Decision FinalDeny"
                  by(simp add: optimize_matches_def split: split_if_asm)
                with Nomatch have IH: "approximating_bigstep_fun ?\<gamma> p rs Undecided = Decision FinalDeny"
                  using simple_ruleset_tail by auto
                with Nomatch(1) show ?thesis by simp
                next
                case True
                  from Nomatch.prems(2) True have 1: "approximating_bigstep_fun ?\<gamma> p
                    (Rule (abstract_primitive disc m) a # (optimize_matches (abstract_primitive disc) rs)) Undecided = Decision FinalDeny"
                    using optimize_matches_matches_fst by metis
                    
                  from Nomatch.prems(1) have "a = action.Accept \<or> a = action.Drop" by(simp add: simple_ruleset_def)
                  from Nomatch.hyps(1) Nomatch.prems(3) abstract_primitive_in_doubt_allow_Allow2[OF generic] have
                    "a = action.Drop \<Longrightarrow> \<not> matches ?\<gamma> (abstract_primitive disc m) action.Drop p" by simp
                  with True \<open>a = action.Accept \<or> a = action.Drop\<close> have "a = action.Accept" by blast
                  with 1 True have False by simp
                  thus ?thesis ..
                qed
            qed(simp_all add: simple_ruleset_def)
      qed
  
      from good approximating_semantics_iff_fun_good_ruleset abstract_primitive_in_doubt_allow_help1 \<open>good_ruleset rs\<close> show ?allow
        unfolding abstract_def by fast
      from good approximating_semantics_iff_fun_good_ruleset abstract_primitive_in_doubt_allow_help2 \<open>good_ruleset rs\<close> \<gamma>_def show ?deny 
        unfolding abstract_def by fast
    qed
  corollary abstract_primitive_in_doubt_allow:
    assumes "\<forall> r \<in> set rs. normalized_nnf_match (get_match r)" and "simple_ruleset rs"
    defines "\<gamma> \<equiv> (common_matcher, in_doubt_allow)" and "abstract disc \<equiv> optimize_matches (abstract_primitive disc)"
    shows   "{p. \<gamma>,p\<turnstile> \<langle>abstract disc rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny} \<subseteq> {p. \<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny}"
      and   "{p. \<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow} \<subseteq> {p. \<gamma>,p\<turnstile> \<langle>abstract disc rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow}"
    unfolding \<gamma>_def abstract_def
    using assms abstract_primitive_in_doubt_allow_generic[OF primitive_matcher_generic_common_matcher] by blast+
end


context
begin
  private lemma abstract_primitive_in_doubt_deny_Deny:
    "primitive_matcher_generic \<beta> \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> 
      matches (\<beta>, in_doubt_deny) m action.Drop p \<Longrightarrow>
      matches (\<beta>, in_doubt_deny) (abstract_primitive disc m) action.Drop p"
     by(induction disc m rule: abstract_primitive.induct)
       (simp_all add: bunch_of_lemmata_about_matches(1) primitive_matcher_generic.Extra_single)
  
  private lemma abstract_primitive_in_doubt_deny_Deny2:
    "primitive_matcher_generic \<beta> \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> 
      \<not> matches (\<beta>, in_doubt_deny) m action.Accept p \<Longrightarrow>
      \<not> matches (\<beta>, in_doubt_deny) (abstract_primitive disc m) action.Accept p"
     proof(induction disc m rule: abstract_primitive.induct)
     case(5 m1 m2) thus ?case by (auto simp add: bunch_of_lemmata_about_matches(1))
     qed(simp_all add: bunch_of_lemmata_about_matches(1) primitive_matcher_generic.Extra_single)
  
  private lemma abstract_primitive_in_doubt_deny_Allow: 
    "primitive_matcher_generic \<beta> \<Longrightarrow> normalized_nnf_match m \<Longrightarrow>
      matches (\<beta>, in_doubt_deny) (abstract_primitive disc m) action.Accept p \<Longrightarrow>
      matches (\<beta>, in_doubt_deny) m action.Accept p"
     apply(induction disc m rule: abstract_primitive.induct)
           apply (simp_all add: bunch_of_lemmata_about_matches(1))
       apply(auto simp add: primitive_matcher_generic.Extra_single primitive_matcher_generic.Extra_single_not split: split_if_asm)
     done
  
  private lemma abstract_primitive_in_doubt_deny_Allow2: 
    "primitive_matcher_generic \<beta> \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> 
      \<not> matches (\<beta>, in_doubt_deny) (abstract_primitive disc m) action.Drop p \<Longrightarrow>
      \<not> matches (\<beta>, in_doubt_deny) m action.Drop p"
     apply(induction disc m rule: abstract_primitive.induct)
           apply (simp_all add: bunch_of_lemmata_about_matches(1))
       apply(auto simp add: primitive_matcher_generic.Extra_single primitive_matcher_generic.Extra_single_not split: split_if_asm)
     done

  theorem abstract_primitive_in_doubt_deny_generic:
    fixes \<beta>::"('i::len common_primitive, ('i, 'a) tagged_packet_scheme) exact_match_tac"
    assumes generic: "primitive_matcher_generic \<beta>"
        and n: "\<forall> r \<in> set rs. normalized_nnf_match (get_match r)"
        and simple: "simple_ruleset rs"
    defines "\<gamma> \<equiv> (\<beta>, in_doubt_deny)" and "abstract disc \<equiv> optimize_matches (abstract_primitive disc)"
    shows   "{p. \<gamma>,p\<turnstile> \<langle>abstract disc rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow} \<subseteq> {p. \<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow}"
             (is ?allow)
    and     "{p. \<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny} \<subseteq> {p. \<gamma>,p\<turnstile> \<langle>abstract disc rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny}"
             (is ?deny)
    proof -
      from simple have "good_ruleset rs" using simple_imp_good_ruleset by fast
      from optimize_matches_simple_ruleset simple simple_imp_good_ruleset have
        good: "good_ruleset (optimize_matches (abstract_primitive disc) rs)" by fast

      let ?\<gamma>="(\<beta>, in_doubt_deny) :: ('i::len common_primitive, ('i, 'a) tagged_packet_scheme) match_tac"
        --\<open>type signature is needed, otherwise @{const in_doubt_allow} would be for arbitrary packet\<close>
      
      have abstract_primitive_in_doubt_deny_help1:
        "approximating_bigstep_fun \<gamma> p (optimize_matches (abstract_primitive disc) rs) Undecided = Decision FinalDeny"
        if prem: "approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny" for p
        proof -
          from simple have "wf_ruleset \<gamma> p rs" using good_imp_wf_ruleset simple_imp_good_ruleset by fast
          from this simple prem n show ?thesis
            unfolding \<gamma>_def
            proof(induction ?\<gamma> p rs Undecided rule: approximating_bigstep_fun_induct_wf)
            case (MatchDrop p m a rs)
              from MatchDrop.prems abstract_primitive_in_doubt_deny_Deny[OF generic] MatchDrop.hyps have
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
                  from Nomatch.prems(1) have "a = action.Accept \<or> a = action.Drop" by(simp add: simple_ruleset_def)
                  from Nomatch.hyps(1) Nomatch.prems(3) abstract_primitive_in_doubt_deny_Deny2[OF generic] have
                    "a = action.Accept \<Longrightarrow> \<not> matches ?\<gamma> (abstract_primitive disc m) action.Accept p" by(simp)
                  with True \<open>a = action.Accept \<or> a = action.Drop\<close> have "a = action.Drop" by blast
                  with True show ?thesis using optimize_matches_matches_fst by fastforce
                qed
            qed(simp_all add: simple_ruleset_def)
      qed

      have abstract_primitive_in_doubt_deny_help2:
        "approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow"
        if prem: "approximating_bigstep_fun \<gamma> p (optimize_matches (abstract_primitive disc) rs) Undecided = Decision FinalAllow"
        for p
        proof -
          from simple have "wf_ruleset ?\<gamma> p rs" using good_imp_wf_ruleset simple_imp_good_ruleset by fast
          from this simple prem n show ?thesis
            unfolding \<gamma>_def
            proof(induction ?\<gamma> p rs Undecided rule: approximating_bigstep_fun_induct_wf)
            case Empty thus ?case by(simp add: optimize_matches_def)
            next
            case (MatchAccept p m a rs) thus ?case by auto
            next
            case (MatchDrop p m a rs)
              from MatchDrop.prems abstract_primitive_in_doubt_deny_Deny[OF generic] MatchDrop.hyps have
                1: "matches ?\<gamma> (abstract_primitive disc m) action.Drop p" by simp
              from MatchDrop have "approximating_bigstep_fun ?\<gamma> p
                (Rule (abstract_primitive disc m) action.Drop # (optimize_matches (abstract_primitive disc) rs)) Undecided = Decision FinalAllow"
              using optimize_matches_matches_fst 1 by fastforce
              with 1 have False by(simp)
              thus ?case ..
            next
            case (Nomatch p m a rs) thus ?case
              proof(cases "matches ?\<gamma> (abstract_primitive disc m) a p")
                case False 
                with Nomatch.prems(2) have "approximating_bigstep_fun ?\<gamma> p (optimize_matches (abstract_primitive disc) rs) Undecided = Decision FinalAllow"
                  by(simp add: optimize_matches_def split: split_if_asm)
                with Nomatch have IH: "approximating_bigstep_fun ?\<gamma> p rs Undecided = Decision FinalAllow"
                  using simple_ruleset_tail by auto
                with Nomatch(1) show ?thesis by simp
                next
                case True
                  from Nomatch.prems(2) True have 1: "approximating_bigstep_fun ?\<gamma> p
                    (Rule (abstract_primitive disc m) a # (optimize_matches (abstract_primitive disc) rs)) Undecided = Decision FinalAllow"
                    using optimize_matches_matches_fst by metis
                  from Nomatch.prems(1) have "a = action.Accept \<or> a = action.Drop" by(simp add: simple_ruleset_def)
                  from Nomatch.hyps(1) Nomatch.prems(3) abstract_primitive_in_doubt_deny_Deny2[OF generic] have
                    "a = action.Accept \<Longrightarrow> \<not> matches ?\<gamma> (abstract_primitive disc m) action.Accept p" by simp
                  with True \<open>a = action.Accept \<or> a = action.Drop\<close> have "a = action.Drop" by blast
                  with 1 True have False by force
                  thus ?thesis ..
                qed
            qed(simp_all add: simple_ruleset_def)
      qed

      from good approximating_semantics_iff_fun_good_ruleset abstract_primitive_in_doubt_deny_help1 \<open>good_ruleset rs\<close> show ?deny
        unfolding abstract_def by fast
      from good approximating_semantics_iff_fun_good_ruleset abstract_primitive_in_doubt_deny_help2 \<open>good_ruleset rs\<close> show ?allow
        unfolding abstract_def by fast
    qed
end



end
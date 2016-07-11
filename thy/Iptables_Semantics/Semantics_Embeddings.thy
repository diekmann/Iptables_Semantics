theory Semantics_Embeddings
imports "Simple_Firewall/SimpleFw_Compliance" Matching_Embeddings Semantics "Semantics_Ternary/Semantics_Ternary"
begin


section\<open>Semantics Embedding\<close>

subsection\<open>Tactic @{const in_doubt_allow}\<close>

lemma iptables_bigstep_undecided_to_undecided_in_doubt_allow_approx:
  assumes agree: "matcher_agree_on_exact_matches \<gamma> \<beta>"
      and good: "good_ruleset rs" and semantics: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
    shows "(\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Undecided \<or> (\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow"
  proof -
    from semantics good show ?thesis
    proof(induction rs Undecided Undecided rule: iptables_bigstep_induct)
      case Skip thus ?case by(auto intro: approximating_bigstep.skip)
      next
      case Log thus ?case by(auto intro: approximating_bigstep.empty approximating_bigstep.log approximating_bigstep.nomatch)
      next
      case (Nomatch m a)
        with not_exact_match_in_doubt_allow_approx_match[OF agree] have
        "a \<noteq> Log \<Longrightarrow> a \<noteq> Empty \<Longrightarrow> a = Accept \<and> Matching_Ternary.matches (\<beta>, in_doubt_allow) m a p \<or> \<not> Matching_Ternary.matches (\<beta>, in_doubt_allow) m a p"
          by(simp add: good_ruleset_alt) blast
      thus ?case
        by(cases a) (auto intro: approximating_bigstep.empty approximating_bigstep.log approximating_bigstep.accept approximating_bigstep.nomatch)
      next
      case (Seq rs rs1 rs2 t)
        from Seq have "good_ruleset rs1" and "good_ruleset rs2" by(simp_all add: good_ruleset_append)
        also from Seq iptables_bigstep_to_undecided have "t = Undecided" by simp
        ultimately show ?case using Seq by(fastforce intro: approximating_bigstep.decision Semantics_Ternary.seq')
    qed(simp_all add: good_ruleset_def)
  qed


lemma FinalAllow_approximating_in_doubt_allow:
   assumes agree: "matcher_agree_on_exact_matches \<gamma> \<beta>"
       and good: "good_ruleset rs" and semantics: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow"
     shows "(\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow"
  proof -
    from semantics good show ?thesis
    proof(induction rs Undecided "Decision FinalAllow" rule: iptables_bigstep_induct)
      case Allow thus ?case
       by (auto intro: agree approximating_bigstep.accept in_doubt_allow_allows_Accept)
      next
      case (Seq rs rs1 rs2 t)
        from Seq have good1: "good_ruleset rs1" and good2: "good_ruleset rs2" by(simp_all add: good_ruleset_append)
        show ?case
        proof(cases t)
          case Decision with Seq good1 good2 show "(\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow"
            by (auto intro: approximating_bigstep.decision approximating_bigstep.seq dest: Semantics.decisionD)
          next
          case Undecided
            with iptables_bigstep_undecided_to_undecided_in_doubt_allow_approx[OF agree good1] Seq have
              "(\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs1, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Undecided \<or> (\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs1, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow" by simp
            with Undecided Seq good1 good2 show "(\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow"
              by (auto intro: approximating_bigstep.seq Semantics_Ternary.seq' approximating_bigstep.decision)
          qed
      next
      case Call_result thus ?case by(simp add: good_ruleset_alt)
    qed
  qed

corollary FinalAllows_subseteq_in_doubt_allow: "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow> good_ruleset rs \<Longrightarrow>
   {p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow} \<subseteq> {p. (\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow}"
using FinalAllow_approximating_in_doubt_allow by (metis (lifting, full_types) Collect_mono)


(*referenced by name in paper*)
corollary new_packets_to_simple_firewall_overapproximation:
  defines "preprocess rs \<equiv> upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new rs)))"
  and "newpkt p \<equiv> match_tcp_flags ipt_tcp_syn (p_tcp_flags p) \<and> p_tag_ctstate p = CT_New"
  fixes p :: "('i::len, 'pkt_ext) tagged_packet_scheme"
  assumes "matcher_agree_on_exact_matches \<gamma> common_matcher" and "simple_ruleset rs"
  shows "{p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow \<and> newpkt p} \<subseteq> {p. simple_fw (to_simple_firewall (preprocess rs)) p = Decision FinalAllow \<and> newpkt p}"
proof -
  from assms(3) have "{p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow \<and> newpkt p} \<subseteq>
      {p. (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
    apply(drule_tac rs=rs and \<Gamma>=\<Gamma> in FinalAllows_subseteq_in_doubt_allow)
     using simple_imp_good_ruleset assms(4) apply blast
    by blast
  thus ?thesis unfolding newpkt_def preprocess_def using transform_simple_fw_upper(2)[OF assms(4)] by blast
qed



lemma approximating_bigstep_undecided_to_undecided_in_doubt_allow_approx: "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow>
       good_ruleset rs \<Longrightarrow>
       (\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Undecided \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided \<or>  \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalDeny"
 apply(rotate_tac 2)
 apply(induction rs Undecided Undecided rule: approximating_bigstep_induct)
    apply(simp_all)
    apply (metis iptables_bigstep.skip)
   apply (metis iptables_bigstep.empty iptables_bigstep.log iptables_bigstep.nomatch)
  apply(simp split: ternaryvalue.split_asm add: matches_case_ternaryvalue_tuple)
   apply (metis in_doubt_allow_allows_Accept iptables_bigstep.nomatch matches_casesE ternaryvalue.distinct(1) ternaryvalue.distinct(5))
  apply(case_tac a)
          apply(simp_all)
         apply (metis iptables_bigstep.drop iptables_bigstep.nomatch)
        apply (metis iptables_bigstep.log iptables_bigstep.nomatch)
       apply (metis iptables_bigstep.nomatch iptables_bigstep.reject)
      apply(simp add: good_ruleset_alt)
     apply(simp add: good_ruleset_alt)
    apply(simp add: good_ruleset_alt)
   apply (metis iptables_bigstep.empty iptables_bigstep.nomatch)
  apply(simp add: good_ruleset_alt)
 apply(simp add: good_ruleset_append,clarify)
 by (metis approximating_bigstep_to_undecided iptables_bigstep.decision iptables_bigstep.seq)

lemma FinalDeny_approximating_in_doubt_allow: "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow>
   good_ruleset rs \<Longrightarrow>
   (\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalDeny"
 apply(rotate_tac 2)
 apply(induction rs Undecided "Decision FinalDeny" rule: approximating_bigstep_induct)
  apply(simp_all)
 apply (metis action.distinct(1) action.distinct(5) deny not_exact_match_in_doubt_allow_approx_match) 
 apply(simp add: good_ruleset_append, clarify)
 apply(case_tac t)
   apply(simp)
   apply(drule(2) approximating_bigstep_undecided_to_undecided_in_doubt_allow_approx[where \<Gamma>=\<Gamma>])
   apply(erule disjE)
    apply (metis iptables_bigstep.seq)
   apply (metis iptables_bigstep.decision iptables_bigstep.seq)
 by (metis Decision_approximating_bigstep_fun approximating_semantics_imp_fun iptables_bigstep.decision iptables_bigstep.seq)


corollary FinalDenys_subseteq_in_doubt_allow: "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow> good_ruleset rs \<Longrightarrow>
   {p. (\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny} \<subseteq> {p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalDeny}"
using FinalDeny_approximating_in_doubt_allow by (metis (lifting, full_types) Collect_mono)

text\<open>
  If our approximating firewall (the executable version) concludes that we deny a packet, 
  the exact semantic agrees that this packet is definitely denied!
\<close>
corollary "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow> good_ruleset rs \<Longrightarrow>
  approximating_bigstep_fun (\<beta>, in_doubt_allow) p rs Undecided = (Decision FinalDeny) \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalDeny"
apply(frule(1) FinalDeny_approximating_in_doubt_allow[where p=p and \<Gamma>=\<Gamma>])
 apply(rule approximating_fun_imp_semantics)
  apply (metis good_imp_wf_ruleset)
 apply(simp_all)
done



subsection\<open>Tactic  @{const in_doubt_deny}\<close>


lemma iptables_bigstep_undecided_to_undecided_in_doubt_deny_approx: "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow>
       good_ruleset rs \<Longrightarrow>
       \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow>
       (\<beta>, in_doubt_deny),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Undecided \<or> (\<beta>, in_doubt_deny),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny"
apply(rotate_tac 2)
apply(induction rs Undecided Undecided rule: iptables_bigstep_induct)
     apply(simp_all)
     apply (metis approximating_bigstep.skip)
    apply (metis approximating_bigstep.empty approximating_bigstep.log approximating_bigstep.nomatch)
   apply(case_tac "a = Log")
    apply (metis approximating_bigstep.log approximating_bigstep.nomatch)
   apply(case_tac "a = Empty")
    apply (metis approximating_bigstep.empty approximating_bigstep.nomatch)
   apply(drule_tac a=a in not_exact_match_in_doubt_deny_approx_match)
     apply(simp_all)
    apply(simp add: good_ruleset_alt)
    apply fast
   apply (metis approximating_bigstep.drop approximating_bigstep.nomatch approximating_bigstep.reject)
  apply(frule iptables_bigstep_to_undecided)
  apply(simp)
  apply(simp add: good_ruleset_append)
  apply (metis (hide_lams, no_types) approximating_bigstep.decision Semantics_Ternary.seq')
 apply(simp add: good_ruleset_def)
apply(simp add: good_ruleset_def)
done


lemma FinalDeny_approximating_in_doubt_deny: "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow>
   good_ruleset rs \<Longrightarrow>
   \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalDeny \<Longrightarrow> (\<beta>, in_doubt_deny),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny"
 apply(rotate_tac 2)
 apply(induction rs Undecided "Decision FinalDeny" rule: iptables_bigstep_induct)
   apply(simp_all)
   apply (metis approximating_bigstep.drop approximating_bigstep.reject in_doubt_deny_denies_DropReject)
   apply(case_tac t)
    apply(simp_all)
    prefer 2
    apply(simp add: good_ruleset_append)
    apply (metis approximating_bigstep.decision approximating_bigstep.seq Semantics.decisionD state.inject)
   apply(thin_tac "False \<Longrightarrow> _ \<Longrightarrow> _")
   apply(simp add: good_ruleset_append, clarify)
   apply(drule(2) iptables_bigstep_undecided_to_undecided_in_doubt_deny_approx)
   apply(erule disjE)
    apply (metis approximating_bigstep.seq)
   apply (metis approximating_bigstep.decision Semantics_Ternary.seq')
 apply(simp add: good_ruleset_alt)
done




lemma approximating_bigstep_undecided_to_undecided_in_doubt_deny_approx: "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow>
       good_ruleset rs \<Longrightarrow>
       (\<beta>, in_doubt_deny),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Undecided \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided \<or>  \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow"
 apply(rotate_tac 2)
 apply(induction rs Undecided Undecided rule: approximating_bigstep_induct)
    apply(simp_all)
    apply (metis iptables_bigstep.skip)
   apply (metis iptables_bigstep.empty iptables_bigstep.log iptables_bigstep.nomatch)
  apply(simp split: ternaryvalue.split_asm add: matches_case_ternaryvalue_tuple)
   apply (metis in_doubt_allow_allows_Accept iptables_bigstep.nomatch matches_casesE ternaryvalue.distinct(1) ternaryvalue.distinct(5))
  apply(case_tac a)
         apply(simp_all)
        apply (metis iptables_bigstep.accept iptables_bigstep.nomatch)
       apply (metis iptables_bigstep.log iptables_bigstep.nomatch)
      apply(simp add: good_ruleset_alt)
     apply(simp add: good_ruleset_alt)
    apply(simp add: good_ruleset_alt)
   apply (metis iptables_bigstep.empty iptables_bigstep.nomatch)
  apply(simp add: good_ruleset_alt)
 apply(simp add: good_ruleset_append,clarify)
 by (metis approximating_bigstep_to_undecided iptables_bigstep.decision iptables_bigstep.seq)

lemma FinalAllow_approximating_in_doubt_deny: "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow>
   good_ruleset rs \<Longrightarrow>
   (\<beta>, in_doubt_deny),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow"
 apply(rotate_tac 2)
 apply(induction rs Undecided "Decision FinalAllow" rule: approximating_bigstep_induct)
  apply(simp_all)
  apply (metis action.distinct(1) action.distinct(5) iptables_bigstep.accept not_exact_match_in_doubt_deny_approx_match)
 apply(simp add: good_ruleset_append, clarify)
 apply(case_tac t)
  apply(simp)
  apply(drule(2) approximating_bigstep_undecided_to_undecided_in_doubt_deny_approx[where \<Gamma>=\<Gamma>])
  apply(erule disjE)
   apply (metis iptables_bigstep.seq)
  apply (metis iptables_bigstep.decision iptables_bigstep.seq)
 by (metis Decision_approximating_bigstep_fun approximating_semantics_imp_fun iptables_bigstep.decision iptables_bigstep.seq)


corollary FinalAllows_subseteq_in_doubt_deny: "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow> good_ruleset rs \<Longrightarrow>
   {p. (\<beta>, in_doubt_deny),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow} \<subseteq> {p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow}"
using FinalAllow_approximating_in_doubt_deny by (metis (lifting, full_types) Collect_mono)



corollary new_packets_to_simple_firewall_underapproximation:
  defines "preprocess rs \<equiv> lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new rs)))"
  and "newpkt p \<equiv> match_tcp_flags ipt_tcp_syn (p_tcp_flags p) \<and> p_tag_ctstate p = CT_New"
  fixes p :: "('i::len, 'pkt_ext) tagged_packet_scheme"
  assumes "matcher_agree_on_exact_matches \<gamma> common_matcher" and "simple_ruleset rs"
  shows "{p. simple_fw (to_simple_firewall (preprocess rs)) p = Decision FinalAllow \<and> newpkt p} \<subseteq> {p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow \<and> newpkt p}"
proof -
  from assms(3) have "{p. (common_matcher, in_doubt_deny),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} \<subseteq>
      {p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow \<and> newpkt p}"
    apply(drule_tac rs=rs and \<Gamma>=\<Gamma> in FinalAllows_subseteq_in_doubt_deny)
     using simple_imp_good_ruleset assms(4) apply blast
    by blast
  thus ?thesis unfolding newpkt_def preprocess_def using transform_simple_fw_lower(2)[OF assms(4)] by blast
qed



subsection\<open>Approximating Closures\<close>

theorem FinalAllowClosure:
  assumes "matcher_agree_on_exact_matches \<gamma> \<beta>" and "good_ruleset rs"
  shows "{p. (\<beta>, in_doubt_deny),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow} \<subseteq> {p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow}"
  and   "{p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow} \<subseteq> {p. (\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow}"  
 apply (metis FinalAllows_subseteq_in_doubt_deny assms)
by (metis FinalAllows_subseteq_in_doubt_allow assms)


theorem FinalDenyClosure:
  assumes "matcher_agree_on_exact_matches \<gamma> \<beta>" and "good_ruleset rs"
  shows "{p. (\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny} \<subseteq> {p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalDeny}"
  and   "{p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalDeny} \<subseteq> {p. (\<beta>, in_doubt_deny),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalDeny}"  
 apply (metis FinalDenys_subseteq_in_doubt_allow assms)
by (metis FinalDeny_approximating_in_doubt_deny assms mem_Collect_eq subsetI)




subsection\<open>Exact Embedding\<close>

lemma LukassLemma: assumes agree: "matcher_agree_on_exact_matches \<gamma> \<beta>"
        and noUnknown: "(\<forall> r \<in> set rs. ternary_ternary_eval (map_match_tac \<beta> p (get_match r)) \<noteq> TernaryUnknown)"
        and good: "good_ruleset rs"
      shows "(\<beta>,\<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow>  \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
proof -
  { fix t --\<open>if we show it for arbitrary @{term t}, we can reuse this fact for the other direction.\<close>
    assume a: "(\<beta>,\<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
    from a good agree noUnknown have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
      proof(induction rs s t rule: approximating_bigstep_induct)
      qed(auto intro: approximating_bigstep.intros iptables_bigstep.intros dest: iptables_bigstepD dest: matches_comply_exact simp: good_ruleset_append)
  } note 1=this
  {
    assume a: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
    obtain x where "approximating_bigstep_fun (\<beta>,\<alpha>) p rs s = x" by simp
    with approximating_fun_imp_semantics[OF good_imp_wf_ruleset[OF good]] have x: "(\<beta>,\<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> x" by fast
    with 1 have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> x" by simp
    with a iptables_bigstep_deterministic have "x = t" by metis
    hence "(\<beta>,\<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t" using x by blast
  } note 2=this
  from 1 2 show ?thesis by blast
qed
  

text\<open>
For rulesets without @{term Call}s, the approximating ternary semantics can perfectly simulate the Boolean semantics.
\<close>
theorem \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c_approximating_bigstep_iff_iptables_bigstep:
  assumes "\<forall>r \<in> set rs. \<forall>c. get_action r \<noteq> Call c"
  shows "((\<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c \<gamma>),\<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow>  \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
apply(rule iffI)
 apply(induction rs s t rule: approximating_bigstep_induct)
       apply(auto intro: iptables_bigstep.intros simp: \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c_matching)[7]
apply(insert assms)
apply(induction rs s t rule: iptables_bigstep_induct)
        apply(auto intro: approximating_bigstep.intros simp: \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c_matching)
done

corollary \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c_approximating_bigstep_fun_iff_iptables_bigstep:
  assumes "good_ruleset rs"
  shows "approximating_bigstep_fun (\<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c \<gamma>,\<alpha>) p rs s = t \<longleftrightarrow>  \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
apply(subst approximating_semantics_iff_fun_good_ruleset[symmetric])
 using assms apply simp
apply(subst \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c_approximating_bigstep_iff_iptables_bigstep[where \<Gamma>=\<Gamma>])
 using assms apply (simp add: good_ruleset_def)
by simp



text\<open>The function @{const optimize_primitive_univ} was only applied to the ternary semantics.
      It is, in fact, also correct for the Boolean semantics, assuming the @{const common_matcher}.\<close>
lemma Semantics_optimize_primitive_univ_common_matcher:
  assumes "matcher_agree_on_exact_matches \<gamma> common_matcher" 
    shows "Semantics.matches \<gamma> (optimize_primitive_univ m) p = Semantics.matches \<gamma> m p"
proof -
  have "(max_word::16 word) =  65535" by(simp add: max_word_def)
  hence port_range: "\<And>s e port. s = 0 \<and> e = 0xFFFF \<longrightarrow> (port::16 word) \<le> 0xFFFF" by simp
  from assms show ?thesis
  apply(induction m rule: optimize_primitive_univ.induct)
  apply(auto elim!: matcher_agree_on_exact_matches_gammaE
             simp add: port_range match_ifaceAny ipset_from_cidr_0 ctstate_is_UNIV)
  done
qed



end

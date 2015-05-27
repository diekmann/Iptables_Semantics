theory Semantics_Embeddings
imports Matching_Embeddings Semantics "Semantics_Ternary/Semantics_Ternary"
begin

section{*Semantics Embedding*}

subsection{*Tactic @{const in_doubt_allow}*}

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
        from Seq have "good_ruleset rs1" and "good_ruleset rs2"
        by(simp_all add: good_ruleset_append)
        also from Seq iptables_bigstep_to_undecided have "t = Undecided" by simp
        ultimately show ?case using Seq by(fastforce intro: approximating_bigstep.decision Semantics_Ternary.seq')
    qed(simp_all add: good_ruleset_def)
  qed

lemma FinalAllow_approximating_in_doubt_allow: "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow>
   good_ruleset rs \<Longrightarrow>
   \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow \<Longrightarrow> (\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow"
 apply(rotate_tac 2)
    apply(induction rs Undecided "Decision FinalAllow" rule: iptables_bigstep_induct)
    apply(simp_all)
   apply (metis approximating_bigstep.accept in_doubt_allow_allows_Accept)
    apply(case_tac t)
    apply(simp_all)
    prefer 2
    apply(simp add: good_ruleset_append)
   apply (metis approximating_bigstep.decision approximating_bigstep.seq Semantics.decisionD state.inject)
   apply(thin_tac "False \<Longrightarrow> _ \<Longrightarrow> _")
   apply(simp add: good_ruleset_append, clarify)
   apply(drule(2) iptables_bigstep_undecided_to_undecided_in_doubt_allow_approx)
    apply(erule disjE)
   apply (metis approximating_bigstep.seq)
  apply (metis approximating_bigstep.decision Semantics_Ternary.seq')
 apply(simp add: good_ruleset_alt)
done


corollary FinalAllows_subseteq_in_doubt_allow: "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow> good_ruleset rs \<Longrightarrow>
   {p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow} \<subseteq> {p. (\<beta>, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow}"
using FinalAllow_approximating_in_doubt_allow by (metis (lifting, full_types) Collect_mono)



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


text{*
  If our approximating firewall (the executable version) concludes that we deny a packet, 
  the exact semantic agrees that this packet is definitely denied!
*}
corollary "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow> good_ruleset rs \<Longrightarrow>
  approximating_bigstep_fun (\<beta>, in_doubt_allow) p rs Undecided = (Decision FinalDeny) \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalDeny"
apply(frule(1) FinalDeny_approximating_in_doubt_allow[where p=p and \<Gamma>=\<Gamma>])
 apply(rule approximating_fun_imp_semantics)
  apply (metis good_imp_wf_ruleset)
 apply(simp_all)
done



subsection{*Tactic  @{const in_doubt_deny}*}


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
    apply(thin_tac "False \<Longrightarrow> _")
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


subsection{*Approximating Closures*}

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




subsection{*Exact Embedding*}

thm matcher_agree_on_exact_matches_def[of \<gamma> \<beta>]
lemma LukassLemma:  "
matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow>
(\<forall> r \<in> set rs. ternary_ternary_eval (map_match_tac \<beta> p (get_match r)) \<noteq> TernaryUnknown) \<Longrightarrow>
good_ruleset rs \<Longrightarrow>
(\<beta>,\<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<Longrightarrow>  \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
apply(simp add: matcher_agree_on_exact_matches_def)
apply(rotate_tac 3)
apply(induction rs s t rule: approximating_bigstep_induct)
      apply(auto intro: approximating_bigstep.intros iptables_bigstep.intros dest: iptables_bigstepD)
    apply (metis iptables_bigstep.accept matcher_agree_on_exact_matches_def matches_comply_exact)
   apply (metis deny matcher_agree_on_exact_matches_def matches_comply_exact)
  apply (metis iptables_bigstep.reject matcher_agree_on_exact_matches_def matches_comply_exact)
 apply (metis iptables_bigstep.nomatch matcher_agree_on_exact_matches_def matches_comply_exact)
by (metis good_ruleset_append iptables_bigstep.seq)



text{*
For rulesets without @{term Call}s, the approximating ternary semantics can perfectly simulate the Boolean semantics.
*}
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


end

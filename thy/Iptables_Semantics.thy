theory Iptables_Semantics
imports Semantics_Embeddings "Semantics_Ternary/Normalized_Matches"
begin

section\<open>Normalizing Rulesets in the Boolean Big Step Semantics\<close>
corollary normalize_rules_dnf_correct_BooleanSemantics: 
  assumes "good_ruleset rs"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>normalize_rules_dnf rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
proof -
  from assms have assm': "good_ruleset (normalize_rules_dnf rs)" by (metis good_ruleset_normalize_rules_dnf) 
  from normalize_rules_dnf_correct assms good_imp_wf_ruleset have
    "\<forall>\<beta> \<alpha>. approximating_bigstep_fun (\<beta>,\<alpha>) p (normalize_rules_dnf rs) s = approximating_bigstep_fun (\<beta>,\<alpha>) p rs s" by fast
  hence 
    "\<forall>\<alpha>. approximating_bigstep_fun (\<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c \<gamma>,\<alpha>) p (normalize_rules_dnf rs) s = approximating_bigstep_fun (\<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c \<gamma>,\<alpha>) p rs s" by fast
  with \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c_approximating_bigstep_fun_iff_iptables_bigstep assms assm' show ?thesis
  by metis
qed

end

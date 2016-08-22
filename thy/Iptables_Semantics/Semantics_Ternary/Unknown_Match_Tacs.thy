theory Unknown_Match_Tacs
imports Matching_Ternary
begin

section\<open>Approximate Matching Tactics\<close>
text\<open>in-doubt-tactics\<close>

fun in_doubt_allow :: "'packet unknown_match_tac" where
  "in_doubt_allow Accept _ = True" |
  "in_doubt_allow Drop _ = False" |
  "in_doubt_allow Reject _ = False" |
  "in_doubt_allow _ _ = undefined"
  (*Call/Return must not appear*)
  (*call rm_LogEmpty first. Log/Empty must not appear here*)
  (*give it a simple_ruleset*)

lemma wf_in_doubt_allow: "wf_unknown_match_tac in_doubt_allow"
  unfolding wf_unknown_match_tac_def by(simp add: fun_eq_iff)



fun in_doubt_deny :: "'packet unknown_match_tac" where
  "in_doubt_deny Accept _ = False" |
  "in_doubt_deny Drop _ = True" |
  "in_doubt_deny Reject _ = True" |
  "in_doubt_deny _ _ = undefined"
  (*Call/Return must not appear*)
  (*call rm_LogEmpty first. Log/Empty must not appear here*)
  (*give it a simple_ruleset*)

lemma wf_in_doubt_deny: "wf_unknown_match_tac in_doubt_deny"
  unfolding wf_unknown_match_tac_def by(simp add: fun_eq_iff)

lemma packet_independent_unknown_match_tacs:
    "packet_independent_\<alpha> in_doubt_allow"
    "packet_independent_\<alpha> in_doubt_deny"
  by(simp_all add: packet_independent_\<alpha>_def)


lemma Drop_neq_Accept_unknown_match_tacs:
      "in_doubt_allow Drop \<noteq> in_doubt_allow Accept"
      "in_doubt_deny Drop \<noteq> in_doubt_deny Accept"
  by(simp_all add: fun_eq_iff)



(* use this more often to simplify existing proofs? *)
corollary matches_induction_case_MatchNot_in_doubt_allow:
      "\<forall> a. matches (\<beta>,in_doubt_allow) m' a p = matches (\<beta>,in_doubt_allow) m a p \<Longrightarrow>
      matches (\<beta>,in_doubt_allow) (MatchNot m') a p = matches (\<beta>,in_doubt_allow) (MatchNot m) a p"
  by(rule  matches_induction_case_MatchNot) (simp_all add: Drop_neq_Accept_unknown_match_tacs packet_independent_unknown_match_tacs)
corollary matches_induction_case_MatchNot_in_doubt_deny:
      "\<forall> a. matches (\<beta>,in_doubt_deny) m' a p = matches (\<beta>,in_doubt_deny) m a p \<Longrightarrow>
      matches (\<beta>,in_doubt_deny) (MatchNot m') a p = matches (\<beta>,in_doubt_deny) (MatchNot m) a p"
  by(rule  matches_induction_case_MatchNot) (simp_all add: Drop_neq_Accept_unknown_match_tacs packet_independent_unknown_match_tacs)

end

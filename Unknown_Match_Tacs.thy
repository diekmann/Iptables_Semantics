theory Unknown_Match_Tacs
imports Matching_Ternary
begin

section{*Approximate Matching Tactics*}
text{*in-doubt-tactics*}

fun in_doubt_allow :: "'packet unknown_match_tac" where
  "in_doubt_allow Accept _ = True" |
  "in_doubt_allow Drop _ = False" |
  "in_doubt_allow Reject _ = False"
  (*Call/Return must not appear*)
  (*call rm_LogEmpty first. Log/Empty must not appear here*)
  (*give it a simple_ruleset*)

lemma wf_in_doubt_allow: "wf_unknown_match_tac in_doubt_allow"
  unfolding wf_unknown_match_tac_def by(simp add: fun_eq_iff)



fun in_doubt_deny :: "'packet unknown_match_tac" where
  "in_doubt_deny Accept _ = False" |
  "in_doubt_deny Drop _ = True" |
  "in_doubt_deny Reject _ = True"
  (*Call/Return must not appear*)
  (*call rm_LogEmpty first. Log/Empty must not appear here*)
  (*give it a simple_ruleset*)

lemma wf_in_doubt_deny: "wf_unknown_match_tac in_doubt_deny"
  unfolding wf_unknown_match_tac_def by(simp add: fun_eq_iff)


end

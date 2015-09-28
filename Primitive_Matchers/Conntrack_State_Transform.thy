theory Conntrack_State_Transform
imports "Common_Primitive_Matcher"
        "../Semantics_Ternary/Semantics_Ternary"
begin


text{*The following function assumes that the packet is in a certain state.*}

fun ctstate_assume_state :: "ctstate \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
  "ctstate_assume_state s (Match (CT_State x)) = (if s \<in> x then MatchAny else MatchNot MatchAny)" |
  "ctstate_assume_state s (Match m) = Match m" |
  "ctstate_assume_state s (MatchNot m) = MatchNot (ctstate_assume_state s m)" |
  "ctstate_assume_state _ MatchAny = MatchAny" |
  "ctstate_assume_state s (MatchAnd m1 m2) = MatchAnd (ctstate_assume_state s m1) (ctstate_assume_state s m2)"

lemma ctstate_assume_state: "p_tag_ctstate p = s \<Longrightarrow>
    matches (common_matcher, \<alpha>) (ctstate_assume_state s m) a p \<longleftrightarrow> matches (common_matcher, \<alpha>) m a p"
apply(rule matches_iff_apply_f)
by(induction m rule: ctstate_assume_state.induct) (simp_all)


definition ctstate_assume_new :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "ctstate_assume_new \<equiv> optimize_matches (ctstate_assume_state CT_New)"

lemma ctstate_assume_new_simple_ruleset: "simple_ruleset rs \<Longrightarrow> simple_ruleset (ctstate_assume_new rs)"
  by (simp add: ctstate_assume_new_def optimize_matches_simple_ruleset)

text{*Usually, the interesting part of a firewall is only about the rules for setting up connections.
      That means, we mostly only care about packets in state @{const CT_New}.
      Use the function @{const ctstate_assume_new} to remove all state matching and just care about
      the connection setup.
      *}
corollary ctstate_assume_new: "p_tag_ctstate p = CT_New \<Longrightarrow> 
  approximating_bigstep_fun (common_matcher, \<alpha>) p (ctstate_assume_new rs) s = approximating_bigstep_fun (common_matcher, \<alpha>) p rs s"
unfolding ctstate_assume_new_def
apply(rule optimize_matches)
apply(simp add: ctstate_assume_state)
done




text{*If we assume the CT State is @{const CT_New}, we can also assume that the TCP SYN flag (@{const ipt_tcp_syn}) is set.*}
(*TODO: move?*)
fun ipt_tcp_flags_assume_flag :: "ipt_tcp_flags \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
  "ipt_tcp_flags_assume_flag flg (Match (L4_Flags x)) = (if ipt_tcp_flags_equal x flg then MatchAny else Match (L4_Flags (match_tcp_flags_conjunct x flg)))" |
  "ipt_tcp_flags_assume_flag flg (Match m) = Match m" |
  "ipt_tcp_flags_assume_flag flg (MatchNot m) = MatchNot (ipt_tcp_flags_assume_flag flg m)" |
  "ipt_tcp_flags_assume_flag _ MatchAny = MatchAny" |
  "ipt_tcp_flags_assume_flag flg (MatchAnd m1 m2) = MatchAnd (ipt_tcp_flags_assume_flag flg m1) (ipt_tcp_flags_assume_flag flg m2)"

lemma ipt_tcp_flags_assume_flag: "match_tcp_flags flg (p_tcp_flags p) \<Longrightarrow>
    matches (common_matcher, \<alpha>) (ipt_tcp_flags_assume_flag flg m) a p \<longleftrightarrow> matches (common_matcher, \<alpha>) m a p"
apply(rule matches_iff_apply_f)
by(induction m rule: ipt_tcp_flags_assume_flag.induct) (simp_all add: ipt_tcp_flags_equal match_tcp_flags_conjunct)

definition ipt_tcp_flags_assume_syn :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "ipt_tcp_flags_assume_syn \<equiv> optimize_matches (ipt_tcp_flags_assume_flag ipt_tcp_syn)"

lemma ipt_tcp_flags_assume_syn_simple_ruleset: "simple_ruleset rs \<Longrightarrow> simple_ruleset (ipt_tcp_flags_assume_syn rs)"
  by (simp add: ipt_tcp_flags_assume_syn_def optimize_matches_simple_ruleset)

corollary ipt_tcp_flags_assume_syn: "match_tcp_flags ipt_tcp_syn (p_tcp_flags p) \<Longrightarrow>
  approximating_bigstep_fun (common_matcher, \<alpha>) p (ipt_tcp_flags_assume_syn rs) s = approximating_bigstep_fun (common_matcher, \<alpha>) p rs s"
unfolding ipt_tcp_flags_assume_syn_def
apply(rule optimize_matches)
apply(simp add: ipt_tcp_flags_assume_flag)
done





definition packet_assume_new :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "packet_assume_new \<equiv> ctstate_assume_new \<circ> ipt_tcp_flags_assume_syn"

lemma packet_assume_new_simple_ruleset: "simple_ruleset rs \<Longrightarrow> simple_ruleset (packet_assume_new rs)"
  by (simp add: packet_assume_new_def ipt_tcp_flags_assume_syn_simple_ruleset ctstate_assume_new_simple_ruleset)

corollary packet_assume_new: "match_tcp_flags ipt_tcp_syn (p_tcp_flags p) \<Longrightarrow> p_tag_ctstate p = CT_New \<Longrightarrow> 
  approximating_bigstep_fun (common_matcher, \<alpha>) p (packet_assume_new rs) s = approximating_bigstep_fun (common_matcher, \<alpha>) p rs s"
unfolding packet_assume_new_def
by (simp add: ctstate_assume_new ipt_tcp_flags_assume_syn)

  



end

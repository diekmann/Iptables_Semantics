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
apply(simp add: ctstate_assume_new_def ctstate_assume_state)
done

end

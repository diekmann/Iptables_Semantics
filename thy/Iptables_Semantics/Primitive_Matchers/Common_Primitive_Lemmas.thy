theory Common_Primitive_Lemmas
imports Common_Primitive_Matcher
        "../Semantics_Ternary/Primitive_Normalization"
begin

section\<open>Further Lemmas about the Common Matcher\<close>

lemma has_unknowns_common_matcher: fixes m::"'i::len common_primitive match_expr"
  shows "has_unknowns common_matcher m \<longleftrightarrow> has_disc is_Extra m"
  proof -
  { fix A and p :: "('i, 'a) tagged_packet_scheme"
    have "common_matcher A p = TernaryUnknown \<longleftrightarrow> is_Extra A"
      by(induction A p rule: common_matcher.induct) (simp_all add: bool_to_ternary_Unknown)
  } hence "\<beta> = (common_matcher::('i::len common_primitive, ('i, 'a) tagged_packet_scheme) exact_match_tac)
            \<Longrightarrow> has_unknowns \<beta> m = has_disc is_Extra m" for \<beta>
  by(induction \<beta> m rule: has_unknowns.induct)
    (simp_all)
  thus ?thesis by simp
qed


(*TODO: move*)
lemma normalize_match_preserves_nodisc:
  "\<not> has_disc disc m \<Longrightarrow> m' \<in> set (normalize_match m) \<Longrightarrow> \<not> has_disc disc m'"
  proof - 
    (*no idea why this statement is necessary*)
    have "\<not> has_disc disc m \<longrightarrow> (\<forall>m' \<in> set (normalize_match m). \<not> has_disc disc m')"
    by(induction m rule: normalize_match.induct) (safe,auto) --"need safe, otherwise simplifier loops"
  thus "\<not> has_disc disc m \<Longrightarrow> m' \<in> set (normalize_match m) \<Longrightarrow> \<not> has_disc disc m'" by blast
qed


(*TODO: move*)
lemma normalize_match_preserves_normalized_n_primitive:
  "normalized_n_primitive (disc, sel) f rst \<Longrightarrow>
        \<forall> r \<in> set (normalize_match rst). normalized_n_primitive (disc, sel) f r"
apply(induction rst rule: normalize_match.induct)
      apply(simp; fail)
     apply(simp; fail)
    apply(simp; fail)
   using normalized_n_primitive.simps(5) apply blast (*simp loops*)
  by simp+


end
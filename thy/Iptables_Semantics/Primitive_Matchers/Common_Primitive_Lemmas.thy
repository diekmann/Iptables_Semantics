theory Common_Primitive_Lemmas
imports Common_Primitive_Matcher
        "../Semantics_Ternary/Primitive_Normalization"
        "../Semantics_Ternary/MatchExpr_Fold"
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



end
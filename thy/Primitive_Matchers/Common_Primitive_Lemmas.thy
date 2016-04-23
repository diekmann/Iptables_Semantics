theory Common_Primitive_Lemmas
imports Common_Primitive_Matcher
        "../Semantics_Ternary/Primitive_Normalization"
begin

section{*Further Lemmas about the Common Matcher*}

lemma has_unknowns_common_matcher: "has_unknowns common_matcher m \<longleftrightarrow> has_disc is_Extra m"
  proof -
  { fix A and p :: "'a simple_packet_scheme"
    have "common_matcher A p = TernaryUnknown \<longleftrightarrow> is_Extra A"
      by(induction A p rule: common_matcher.induct) (simp_all add: bool_to_ternary_Unknown)
  } thus ?thesis
  by(induction common_matcher m rule: has_unknowns.induct) (simp_all)
qed

end
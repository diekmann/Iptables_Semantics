theory IPPortSpace_Operations
imports IPSpace_Operations "../Primitive_Matchers/Common_Primitive_Matcher" "../Semantics_Ternary/Matching_Ternary"
begin



definition intersect_ports :: "ipt_ports \<Rightarrow> ipt_ports \<Rightarrow> ipt_ports" where
  "intersect_ports ps1 ps2 = br2l (wordinterval_intersection (l2br ps1) (l2br ps2))"

lemma intersect_ports_correct:
      "common_matcher (Src_Ports ps1) p = TernaryTrue \<and> common_matcher (Src_Ports ps2) p = TernaryTrue \<longleftrightarrow>
       common_matcher (Src_Ports (intersect_ports ps1 ps2)) p = TernaryTrue"
      "common_matcher (Dst_Ports ps1) p = TernaryTrue \<and> common_matcher (Dst_Ports ps2) p = TernaryTrue \<longleftrightarrow>
       common_matcher (Dst_Ports (intersect_ports ps1 ps2)) p = TernaryTrue"
by(simp_all add: intersect_ports_def bool_to_ternary_simps ports_to_set_wordinterval l2br_br2l)


definition negate_ports :: "ipt_ports \<Rightarrow> ipt_ports" where
  "negate_ports ps = br2l (wordinterval_invert (l2br ps))"

lemma negate_ports_correct:
      "common_matcher (Src_Ports ps) p = TernaryTrue \<longleftrightarrow> common_matcher (Src_Ports (negate_ports ps)) p = TernaryFalse"
      "common_matcher (Dst_Ports ps) p = TernaryTrue \<longleftrightarrow> common_matcher (Dst_Ports (negate_ports ps)) p = TernaryFalse"
by(simp_all add: negate_ports_def bool_to_ternary_simps ports_to_set_wordinterval l2br_br2l)



end

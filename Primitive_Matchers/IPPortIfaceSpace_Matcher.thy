theory IPPortIfaceSpace_Matcher
imports "../Semantics_Ternary" IPPortIfaceSpace_Syntax IPSpace_Matcher "../Bitmagic/IPv4Addr" "../Unknown_Match_Tacs"
begin


subsection{*Primitive Matchers: IP Port Iface Matcher*}

fun ipportiface_matcher :: "(ipportiface_rule_match, simple_packet) exact_match_tac" where
  "ipportiface_matcher (IIface i) p = bool_to_ternary (match_iface i (p_iiface p))" |
  "ipportiface_matcher (OIface i) p = bool_to_ternary (match_iface i (p_oiface p))" |

  "ipportiface_matcher (Src ip) p = bool_to_ternary (p_src p \<in> ipv4s_to_set ip)" |
  "ipportiface_matcher (Dst ip) p = bool_to_ternary (p_dst p \<in> ipv4s_to_set ip)" |

  "ipportiface_matcher (Prot proto) p = bool_to_ternary (match_proto proto (p_proto p))" |

  "ipportiface_matcher (Src_Ports ps) p = bool_to_ternary (p_sport p \<in> ports_to_set ps)" |
  "ipportiface_matcher (Dst_Ports ps) p = bool_to_ternary (p_dport p \<in> ports_to_set ps)" |

  "ipportiface_matcher (Extra _) p = TernaryUnknown"




text{*Lemmas when matching on @{term Src} or @{term Dst}*}
lemma ipportiface_matcher_SrcDst_defined:
  "ipportiface_matcher (Src m) p \<noteq> TernaryUnknown"
  "ipportiface_matcher (Dst m) p \<noteq> TernaryUnknown"
  "ipportiface_matcher (Src_Ports ps) p \<noteq> TernaryUnknown"
  "ipportiface_matcher (Dst_Ports ps) p \<noteq> TernaryUnknown"
  apply(case_tac [!] m)
  apply(simp_all add: bool_to_ternary_Unknown)
  done
lemma ipportiface_matcher_SrcDst_defined_simp:
  "ipportiface_matcher (Src x) p \<noteq> TernaryFalse \<longleftrightarrow> ipportiface_matcher (Src x) p = TernaryTrue"
  "ipportiface_matcher (Dst x) p \<noteq> TernaryFalse \<longleftrightarrow> ipportiface_matcher (Dst x) p = TernaryTrue"
apply (metis eval_ternary_Not.cases ipportiface_matcher_SrcDst_defined(1) ternaryvalue.distinct(1))
apply (metis eval_ternary_Not.cases ipportiface_matcher_SrcDst_defined(2) ternaryvalue.distinct(1))
done
lemma match_simplematcher_SrcDst:
  "matches (ipportiface_matcher, \<alpha>) (Match (Src X)) a p \<longleftrightarrow> p_src  p \<in> ipv4s_to_set X"
  "matches (ipportiface_matcher, \<alpha>) (Match (Dst X)) a p \<longleftrightarrow> p_dst  p \<in> ipv4s_to_set X"
   apply(simp_all add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)
   apply (metis bool_to_ternary.elims bool_to_ternary_Unknown ternaryvalue.distinct(1))+
   done
lemma match_simplematcher_SrcDst_not:
  "matches (ipportiface_matcher, \<alpha>) (MatchNot (Match (Src X))) a p \<longleftrightarrow> p_src  p \<notin> ipv4s_to_set X"
  "matches (ipportiface_matcher, \<alpha>) (MatchNot (Match (Dst X))) a p \<longleftrightarrow> p_dst  p \<notin> ipv4s_to_set X"
   apply(simp_all add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)
   apply(case_tac [!] X)
   apply(simp_all add: bool_to_ternary_simps)
   done
lemma ipportiface_matcher_SrcDst_Inter:
  "(\<forall>m\<in>set X. matches (ipportiface_matcher, \<alpha>) (Match (Src m)) a p) \<longleftrightarrow> p_src p \<in> (\<Inter>x\<in>set X. ipv4s_to_set x)"
  "(\<forall>m\<in>set X. matches (ipportiface_matcher, \<alpha>) (Match (Dst m)) a p) \<longleftrightarrow> p_dst p \<in> (\<Inter>x\<in>set X. ipv4s_to_set x)"
  apply(simp_all)
  apply(simp_all add: matches_case_ternaryvalue_tuple bool_to_ternary_Unknown bool_to_ternary_simps split: ternaryvalue.split)
 done



end

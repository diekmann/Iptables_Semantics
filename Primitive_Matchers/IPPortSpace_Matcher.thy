theory IPPortSpace_Matcher
imports "../Semantics_Ternary" IPPortSpace_Syntax IPSpace_Matcher "../Bitmagic/IPv4Addr" "../Unknown_Match_Tacs"
begin




subsection{*Primitive Matchers: IP Port Space Matcher*}

fun ipport_matcher :: "(ipport_rule_match, packet_with_ports) exact_match_tac" where
  "ipport_matcher (Src ip) p = bool_to_ternary (src_ip p \<in> ipv4s_to_set ip)" |

  "ipport_matcher (Dst ip) p = bool_to_ternary (dst_ip p \<in> ipv4s_to_set ip)" |

  "ipport_matcher (Prot ProtAll) _ = TernaryTrue" |
  "ipport_matcher (Prot ipt_protocol.ProtTCP) p = bool_to_ternary (prot p = protPacket.ProtTCP)" |
  "ipport_matcher (Prot ipt_protocol.ProtUDP) p = bool_to_ternary (prot p = protPacket.ProtUDP)" |

  "ipport_matcher (Src_Port ps) p = bool_to_ternary (src_port p \<in> ports_to_set ps)" |

  "ipport_matcher (Dst_Port ps) p = bool_to_ternary (dst_port p \<in> ports_to_set ps)" |

  "ipport_matcher (Extra _) p = TernaryUnknown"




text{*Lemmas when matching on @{term Src} or @{term Dst}*}
lemma ipport_matcher_SrcDst_defined: "ipport_matcher (Src m) p \<noteq> TernaryUnknown" "ipport_matcher (Dst m) p \<noteq> TernaryUnknown"
  apply(case_tac [!] m)
  apply(simp_all add: bool_to_ternary_Unknown)
  done
lemma ipport_matcher_SrcDst_defined_simp:
  "ipport_matcher (Src x) p \<noteq> TernaryFalse \<longleftrightarrow> ipport_matcher (Src x) p = TernaryTrue"
  "ipport_matcher (Dst x) p \<noteq> TernaryFalse \<longleftrightarrow> ipport_matcher (Dst x) p = TernaryTrue"
apply (metis eval_ternary_Not.cases ipport_matcher_SrcDst_defined(1) ternaryvalue.distinct(1))
apply (metis eval_ternary_Not.cases ipport_matcher_SrcDst_defined(2) ternaryvalue.distinct(1))
done
lemma match_simplematcher_SrcDst:
  "matches (ipport_matcher, \<alpha>) (Match (Src X)) a p \<longleftrightarrow> src_ip  p \<in> ipv4s_to_set X"
  "matches (ipport_matcher, \<alpha>) (Match (Dst X)) a p \<longleftrightarrow> dst_ip  p \<in> ipv4s_to_set X"
   apply(simp_all add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)
   apply (metis bool_to_ternary.elims bool_to_ternary_Unknown ternaryvalue.distinct(1))+
   done
lemma match_simplematcher_SrcDst_not:
  "matches (ipport_matcher, \<alpha>) (MatchNot (Match (Src X))) a p \<longleftrightarrow> src_ip  p \<notin> ipv4s_to_set X"
  "matches (ipport_matcher, \<alpha>) (MatchNot (Match (Dst X))) a p \<longleftrightarrow> dst_ip  p \<notin> ipv4s_to_set X"
   apply(simp_all add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)
   apply(case_tac [!] X)
   apply(simp_all add: bool_to_ternary_simps)
   done
lemma ipport_matcher_SrcDst_Inter:
  "(\<forall>m\<in>set X. matches (ipport_matcher, \<alpha>) (Match (Src m)) a p) \<longleftrightarrow> src_ip p \<in> (\<Inter>x\<in>set X. ipv4s_to_set x)"
  "(\<forall>m\<in>set X. matches (ipport_matcher, \<alpha>) (Match (Dst m)) a p) \<longleftrightarrow> dst_ip p \<in> (\<Inter>x\<in>set X. ipv4s_to_set x)"
  apply(simp_all)
  apply(simp_all add: matches_case_ternaryvalue_tuple bool_to_ternary_Unknown bool_to_ternary_simps split: ternaryvalue.split)
 done


end

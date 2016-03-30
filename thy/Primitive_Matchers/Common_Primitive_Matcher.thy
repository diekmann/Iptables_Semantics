theory Common_Primitive_Matcher
imports "../Semantics_Ternary/Semantics_Ternary" Common_Primitive_Syntax "../Bitmagic/IPv4Addr" "../Semantics_Ternary/Unknown_Match_Tacs"
begin


subsection{*Primitive Matchers: IP Port Iface Matcher*}

fun common_matcher :: "(common_primitive, simple_packet) exact_match_tac" where
  "common_matcher (IIface i) p = bool_to_ternary (match_iface i (p_iiface p))" |
  "common_matcher (OIface i) p = bool_to_ternary (match_iface i (p_oiface p))" |

  "common_matcher (Src ip) p = bool_to_ternary (p_src p \<in> ipv4s_to_set ip)" |
  "common_matcher (Dst ip) p = bool_to_ternary (p_dst p \<in> ipv4s_to_set ip)" |

  "common_matcher (Prot proto) p = bool_to_ternary (match_proto proto (p_proto p))" |

  "common_matcher (Src_Ports ps) p = bool_to_ternary (p_sport p \<in> ports_to_set ps)" |
  "common_matcher (Dst_Ports ps) p = bool_to_ternary (p_dport p \<in> ports_to_set ps)" |

  "common_matcher (L4_Flags flags) p = bool_to_ternary (match_tcp_flags flags (p_tcp_flags p))" |

  "common_matcher (CT_State S) p = bool_to_ternary (match_ctstate S (p_tag_ctstate p))" |

  "common_matcher (Extra _) p = TernaryUnknown"



  (* What if we specify a port range where the start port is greater than the end port?
    For example, mathematically, {3 .. 2} = {}. Does iptables have the same behavior?
    For example, --source-port 1:0 raises an error on my system. For normal port specification, -m tcp, and -m multiport.
    There is also a manpage which states "if the first port is greater than the second one they will be swapped."
    I also saw a system where such an empty port range (--source-port 1:0) was really this impossible range and caused a rule that could never match.
    Because \<nexists> port. port \<in> {}.
    The behaviour if the end of the port range is smaller than the start is not 100% consistent among iptables versions and different modules.
    In general, it would be best to raise an error if such a range occurs.
    *)

  text{*Warning: beware of the sloppy term `empty' portrange*}
  text{*An `empty' port range means it can never match! Basically, @{term "MatchNot (Match (Src_Ports [(0,65535)]))"} is False*}
  lemma "\<not> matches (common_matcher, \<alpha>) (MatchNot (Match (Src_Ports [(0,65535)]))) a 
          \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (173,194,112,111),
                   p_proto=TCP, p_sport=2065, p_dport=80, p_tcp_flags = {}, p_tag_ctstate = CT_New\<rparr>"
  (*<*)by(simp add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)(*>*)
  text{*An `empty' port range means it always matches! Basically, @{term "(MatchNot (Match (Src_Ports [])))"} is True.
        This corresponds to firewall behavior, but usually you cannot specify an empty portrange in firewalls, but omission of portrange means no-port-restrictions, 
        i.e. every port matches.*}
  lemma "matches (common_matcher, \<alpha>) (MatchNot (Match (Src_Ports []))) a 
          \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (173,194,112,111),
                   p_proto=TCP, p_sport=2065, p_dport=80, p_tcp_flags = {}, p_tag_ctstate = CT_New\<rparr>"
  (*<*)by(simp add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)(*>*)
  text{*If not a corner case, portrange matching is straight forward.*}
  lemma "matches (common_matcher, \<alpha>) (Match (Src_Ports [(1024,4096), (9999, 65535)])) a 
          \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (173,194,112,111),
                   p_proto=TCP, p_sport=2065, p_dport=80, p_tcp_flags = {}, p_tag_ctstate = CT_New\<rparr>"
        "\<not> matches (common_matcher, \<alpha>) (Match (Src_Ports [(1024,4096), (9999, 65535)])) a 
          \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (173,194,112,111),
                   p_proto=TCP, p_sport=5000, p_dport=80, p_tcp_flags = {}, p_tag_ctstate = CT_New\<rparr>"
        "\<not>matches (common_matcher, \<alpha>) (MatchNot (Match (Src_Ports [(1024,4096), (9999, 65535)]))) a 
          \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (173,194,112,111),
                   p_proto=TCP, p_sport=2065, p_dport=80, p_tcp_flags = {}, p_tag_ctstate = CT_New\<rparr>"
  (*<*)by(simp_all add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)(*>*)
  



lemma packet_independent_\<beta>_unknown_common_matcher: "packet_independent_\<beta>_unknown common_matcher"
  apply(simp add: packet_independent_\<beta>_unknown_def)
  apply(clarify)
  apply(rename_tac a p1 p2)
  by(case_tac a,simp_all add: bool_to_ternary_Unknown)



text{*Lemmas when matching on @{term Src} or @{term Dst}*}
lemma common_matcher_SrcDst_defined:
  "common_matcher (Src m) p \<noteq> TernaryUnknown"
  "common_matcher (Dst m) p \<noteq> TernaryUnknown"
  "common_matcher (Src_Ports ps) p \<noteq> TernaryUnknown"
  "common_matcher (Dst_Ports ps) p \<noteq> TernaryUnknown"
  apply(case_tac [!] m)
  apply(simp_all add: bool_to_ternary_Unknown)
  done
lemma common_matcher_SrcDst_defined_simp:
  "common_matcher (Src x) p \<noteq> TernaryFalse \<longleftrightarrow> common_matcher (Src x) p = TernaryTrue"
  "common_matcher (Dst x) p \<noteq> TernaryFalse \<longleftrightarrow> common_matcher (Dst x) p = TernaryTrue"
apply (metis eval_ternary_Not.cases common_matcher_SrcDst_defined(1) ternaryvalue.distinct(1))
apply (metis eval_ternary_Not.cases common_matcher_SrcDst_defined(2) ternaryvalue.distinct(1))
done
lemma match_simplematcher_SrcDst:
  "matches (common_matcher, \<alpha>) (Match (Src X)) a p \<longleftrightarrow> p_src  p \<in> ipv4s_to_set X"
  "matches (common_matcher, \<alpha>) (Match (Dst X)) a p \<longleftrightarrow> p_dst  p \<in> ipv4s_to_set X"
   apply(simp_all add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)
   apply (metis bool_to_ternary.elims bool_to_ternary_Unknown ternaryvalue.distinct(1))+
   done
lemma match_simplematcher_SrcDst_not:
  "matches (common_matcher, \<alpha>) (MatchNot (Match (Src X))) a p \<longleftrightarrow> p_src  p \<notin> ipv4s_to_set X"
  "matches (common_matcher, \<alpha>) (MatchNot (Match (Dst X))) a p \<longleftrightarrow> p_dst  p \<notin> ipv4s_to_set X"
   apply(simp_all add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)
   apply(case_tac [!] X)
   apply(simp_all add: bool_to_ternary_simps)
   done
lemma common_matcher_SrcDst_Inter:
  "(\<forall>m\<in>set X. matches (common_matcher, \<alpha>) (Match (Src m)) a p) \<longleftrightarrow> p_src p \<in> (\<Inter>x\<in>set X. ipv4s_to_set x)"
  "(\<forall>m\<in>set X. matches (common_matcher, \<alpha>) (Match (Dst m)) a p) \<longleftrightarrow> p_dst p \<in> (\<Inter>x\<in>set X. ipv4s_to_set x)"
  by(simp_all add: matches_case_ternaryvalue_tuple bool_to_ternary_Unknown bool_to_ternary_simps split: ternaryvalue.split)
lemma match_simplematcher_Iface:
  "matches (common_matcher, \<alpha>) (Match (IIface X)) a p \<longleftrightarrow> match_iface X (p_iiface p)"
  "matches (common_matcher, \<alpha>) (Match (OIface X)) a p \<longleftrightarrow> match_iface X (p_oiface p)"
   by(simp_all add: matches_case_ternaryvalue_tuple bool_to_ternary_Unknown bool_to_ternary_simps split: ternaryvalue.split)
text{*Since matching on the iface cannot be @{const TernaryUnknown}*, we can pull out negations.*}
lemma match_simplematcher_Iface_not:
  "matches (common_matcher, \<alpha>) (MatchNot (Match (IIface X))) a p \<longleftrightarrow> \<not> match_iface X (p_iiface p)"
  "matches (common_matcher, \<alpha>) (MatchNot (Match (OIface X))) a p \<longleftrightarrow> \<not> match_iface X (p_oiface p)"
   by(simp_all add: matches_case_ternaryvalue_tuple bool_to_ternary_simps split: ternaryvalue.split)


lemma match_simplematcher_Prot:
  "matches (common_matcher, \<alpha>) (Match (Prot X)) a p \<longleftrightarrow> match_proto X (p_proto p)"
   by(simp_all add: matches_case_ternaryvalue_tuple bool_to_ternary_Unknown bool_to_ternary_simps split: ternaryvalue.split)
lemma match_simplematcher_Prot_not:
  "matches (common_matcher, \<alpha>) (MatchNot (Match (Prot X))) a p \<longleftrightarrow> \<not> match_proto X (p_proto p)"
   by(simp_all add: matches_case_ternaryvalue_tuple bool_to_ternary_simps split: ternaryvalue.split)



text{* multiport list is a way to express  disjunction in one matchexpression in some firewalls*}
lemma multiports_disjuction:
        "(\<exists>rg\<in>set spts. matches (common_matcher, \<alpha>) (Match (Src_Ports [rg])) a p) \<longleftrightarrow>
        matches (common_matcher, \<alpha>) (Match (Src_Ports spts)) a p"
        "(\<exists>rg\<in>set dpts. matches (common_matcher, \<alpha>) (Match (Dst_Ports [rg])) a p) \<longleftrightarrow>
        matches (common_matcher, \<alpha>) (Match (Dst_Ports dpts)) a p"
  apply(simp_all add: bool_to_ternary_Unknown matches_case_ternaryvalue_tuple bunch_of_lemmata_about_matches bool_to_ternary_simps split: ternaryvalue.split ternaryvalue.split_asm)
  apply(simp_all add: ports_to_set)
  apply(safe) (*ugly proof*)
     apply force+
  done


subsection{*Basic optimisations*}
  text{*Perform very basic optimization. Remove matches to primitives which are essentially @{const MatchAny}*}
  fun optimize_primitive_univ :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
    "optimize_primitive_univ (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) = MatchAny" |
    "optimize_primitive_univ (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) = MatchAny" |
    "optimize_primitive_univ (Match (IIface iface)) = (if iface = ifaceAny then MatchAny else (Match (IIface iface)))" |
    "optimize_primitive_univ (Match (OIface iface)) = (if iface = ifaceAny then MatchAny else (Match (OIface iface)))" |
    "optimize_primitive_univ (Match (Src_Ports [(s, e)])) = (if s = 0 \<and> e = 0xFFFF then MatchAny else (Match (Src_Ports [(s, e)])))" |
    "optimize_primitive_univ (Match (Dst_Ports [(s, e)])) = (if s = 0 \<and> e = 0xFFFF then MatchAny else (Match (Dst_Ports [(s, e)])))" |
    "optimize_primitive_univ (Match (Prot ProtoAny)) = MatchAny" |
    "optimize_primitive_univ (Match (L4_Flags (TCP_Flags m c))) = (if m = {} \<and> c = {} then MatchAny else (Match (L4_Flags (TCP_Flags m c))))" |
    "optimize_primitive_univ (Match (CT_State ctstate)) = (if ctstate_is_UNIV ctstate then MatchAny else Match (CT_State ctstate))" |
    "optimize_primitive_univ (Match m) = Match m" |
    (*"optimize_primitive_univ (MatchNot (MatchNot m)) = (optimize_primitive_univ m)" | --"needed to preserve normalized condition"*)
    "optimize_primitive_univ (MatchNot m) = (MatchNot (optimize_primitive_univ m))" |
    (*"optimize_primitive_univ (MatchAnd (Match (Extra e1)) (Match (Extra e2))) = optimize_primitive_univ (Match (Extra (e1@'' ''@e2)))" |
      -- "can be done but normalization does not work afterwards"*)
    "optimize_primitive_univ (MatchAnd m1 m2) = MatchAnd (optimize_primitive_univ m1) (optimize_primitive_univ m2)" |
    "optimize_primitive_univ MatchAny = MatchAny"

    lemma optimize_primitive_univ_unchanged_primitives:
    "optimize_primitive_univ (Match a) = (Match a) \<or> optimize_primitive_univ (Match a) = MatchAny"
      by (induction "(Match a)" rule: optimize_primitive_univ.induct) (auto split: split_if_asm)
  
  lemma optimize_primitive_univ_correct_matchexpr: "matches (common_matcher, \<alpha>) m = matches (common_matcher, \<alpha>) (optimize_primitive_univ m)"
    proof(simp add: fun_eq_iff, clarify, rename_tac a p)
      fix a p
      have "(max_word::16 word) =  65535" by(simp add: max_word_def)
      hence port_range: "\<And>s e port. s = 0 \<and> e = 0xFFFF \<longrightarrow> (port::16 word) \<le> 0xFFFF" by simp
      have "ternary_ternary_eval (map_match_tac common_matcher p m) = ternary_ternary_eval (map_match_tac common_matcher p (optimize_primitive_univ m))"
        apply(induction m rule: optimize_primitive_univ.induct)
        apply(simp_all add: port_range match_ifaceAny ip_in_ipv4range_set_from_prefix_UNIV ctstate_is_UNIV)
        done
      thus "matches (common_matcher, \<alpha>) m a p = matches (common_matcher, \<alpha>) (optimize_primitive_univ m) a p"
        by(rule matches_iff_apply_f)
      qed
  
  corollary optimize_primitive_univ_correct: "approximating_bigstep_fun (common_matcher, \<alpha>) p (optimize_matches optimize_primitive_univ rs) s = 
                                              approximating_bigstep_fun (common_matcher, \<alpha>) p rs s"
  using optimize_matches optimize_primitive_univ_correct_matchexpr by metis
  
  
  
  (*TODO: move
    TODO: this is currently not used.*)
  text{*Compress many @{const Extra} expressions to one expression.*}
  fun compress_extra :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
    "compress_extra (Match x) = Match x" |
    "compress_extra (MatchNot (Match (Extra e))) = Match (Extra (''NOT (''@e@'')''))" |
    "compress_extra (MatchNot m) = (MatchNot (compress_extra m))" |
    (*"compress_extra (MatchAnd (Match (Extra e1)) (Match (Extra e2))) = compress_extra (Match (Extra (e1@'' ''@e2)))" |*)
    (*"compress_extra (MatchAnd (Match (Extra e1)) MatchAny) = Match (Extra e1)" |*)
    "compress_extra (MatchAnd (Match (Extra e1)) m2) = (case compress_extra m2 of Match (Extra e2) \<Rightarrow> Match (Extra (e1@'' ''@e2)) | MatchAny \<Rightarrow> Match (Extra e1) | m2' \<Rightarrow> MatchAnd (Match (Extra e1)) m2')" |
    "compress_extra (MatchAnd m1 m2) = MatchAnd (compress_extra m1) (compress_extra m2)" |
    (*"compress_extra (MatchAnd m1 m2) = (case (compress_extra m1, compress_extra m2) of 
          (Match (Extra e1), Match (Extra e2)) \<Rightarrow> Match (Extra (e1@'' ''@e2))
        | (Match (Extra e1), MatchAny) \<Rightarrow> Match (Extra e1)
        | (MatchAny, Match (Extra e2)) \<Rightarrow> Match (Extra e2)
        | (m1', m2') \<Rightarrow> MatchAnd m1' m2')" |*)
    "compress_extra MatchAny = MatchAny"
  
  thm compress_extra.simps
  
  value "compress_extra (MatchAnd (Match (Extra ''foo'')) (Match (Extra ''bar'')))"
  value "compress_extra (MatchAnd (Match (Extra ''foo'')) (MatchNot (Match (Extra ''bar''))))"
  value "compress_extra (MatchAnd (Match (Extra ''-m'')) (MatchAnd (Match (Extra ''addrtype'')) (MatchAnd (Match (Extra ''--dst-type'')) (MatchAnd (Match (Extra ''BROADCAST'')) MatchAny))))"
  
  lemma compress_extra_correct_matchexpr: "matches (common_matcher, \<alpha>) m = matches (common_matcher, \<alpha>) (compress_extra m)"
    proof(simp add: fun_eq_iff, clarify, rename_tac a p)
      fix a p
      have "ternary_ternary_eval (map_match_tac common_matcher p m) = ternary_ternary_eval (map_match_tac common_matcher p (compress_extra m))"
        apply(induction m rule: compress_extra.induct)
        apply (simp_all)
        (*apply(simp_all add: eval_ternary_simps)*)
        apply(simp_all split: match_expr.split match_expr.split_asm common_primitive.split)
        (*apply(simp_all add: eval_ternary_simps_simple)*)
        done (*TODO: tune proof*)
      thus "matches (common_matcher, \<alpha>) m a p = matches (common_matcher, \<alpha>) (compress_extra m) a p"
        by(rule matches_iff_apply_f)
      qed





subsection{*Abstracting over unknowns*}
  text{*remove @{const Extra} (i.e. @{const TernaryUnknown}) match expressions*}
  fun upper_closure_matchexpr :: "action \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
    "upper_closure_matchexpr _ MatchAny = MatchAny" |
    "upper_closure_matchexpr Accept (Match (Extra _)) = MatchAny" |
    "upper_closure_matchexpr Reject (Match (Extra _)) = MatchNot MatchAny" |
    "upper_closure_matchexpr Drop (Match (Extra _)) = MatchNot MatchAny" |
    "upper_closure_matchexpr _ (Match m) = Match m" |
    "upper_closure_matchexpr Accept (MatchNot (Match (Extra _))) = MatchAny" |
    "upper_closure_matchexpr Drop (MatchNot (Match (Extra _))) = MatchNot MatchAny" |
    "upper_closure_matchexpr Reject (MatchNot (Match (Extra _))) = MatchNot MatchAny" |
    "upper_closure_matchexpr a (MatchNot (MatchNot m)) = upper_closure_matchexpr a m" |
    "upper_closure_matchexpr a (MatchNot (MatchAnd m1 m2)) = 
      (let m1' = upper_closure_matchexpr a (MatchNot m1); m2' = upper_closure_matchexpr a (MatchNot m2) in
      (if m1' = MatchAny \<or> m2' = MatchAny
       then MatchAny
       else 
          if m1' = MatchNot MatchAny then m2' else
          if m2' = MatchNot MatchAny then m1'
       else
          MatchNot (MatchAnd (MatchNot m1') (MatchNot m2')))
         )" |
    "upper_closure_matchexpr _ (MatchNot m) = MatchNot m" | 
    "upper_closure_matchexpr a (MatchAnd m1 m2) = MatchAnd (upper_closure_matchexpr a m1) (upper_closure_matchexpr a m2)"
  
  lemma upper_closure_matchexpr_generic: 
    "a = Accept \<or> a = Drop \<Longrightarrow> remove_unknowns_generic (common_matcher, in_doubt_allow) a m = upper_closure_matchexpr a m"
    by(induction a m rule: upper_closure_matchexpr.induct)
    (simp_all add: unknown_match_all_def unknown_not_match_any_def bool_to_ternary_Unknown)
  
  
  
  fun lower_closure_matchexpr :: "action \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
    "lower_closure_matchexpr _ MatchAny = MatchAny" |
    "lower_closure_matchexpr Accept (Match (Extra _)) = MatchNot MatchAny" |
    "lower_closure_matchexpr Reject (Match (Extra _)) = MatchAny" |
    "lower_closure_matchexpr Drop (Match (Extra _)) = MatchAny" |
    "lower_closure_matchexpr _ (Match m) = Match m" |
    "lower_closure_matchexpr Accept (MatchNot (Match (Extra _))) = MatchNot MatchAny" |
    "lower_closure_matchexpr Drop (MatchNot (Match (Extra _))) = MatchAny" |
    "lower_closure_matchexpr Reject (MatchNot (Match (Extra _))) = MatchAny" |
    "lower_closure_matchexpr a (MatchNot (MatchNot m)) = lower_closure_matchexpr a m" |
    "lower_closure_matchexpr a (MatchNot (MatchAnd m1 m2)) = 
      (let m1' = lower_closure_matchexpr a (MatchNot m1); m2' = lower_closure_matchexpr a (MatchNot m2) in
      (if m1' = MatchAny \<or> m2' = MatchAny
       then MatchAny
       else 
          if m1' = MatchNot MatchAny then m2' else
          if m2' = MatchNot MatchAny then m1'
       else
          MatchNot (MatchAnd (MatchNot m1') (MatchNot m2')))
         )" |
    "lower_closure_matchexpr _ (MatchNot m) = MatchNot m" | 
    "lower_closure_matchexpr a (MatchAnd m1 m2) = MatchAnd (lower_closure_matchexpr a m1) (lower_closure_matchexpr a m2)"
  
  lemma lower_closure_matchexpr_generic: 
    "a = Accept \<or> a = Drop \<Longrightarrow> remove_unknowns_generic (common_matcher, in_doubt_deny) a m = lower_closure_matchexpr a m"
    by(induction a m rule: lower_closure_matchexpr.induct)
    (simp_all add: unknown_match_all_def unknown_not_match_any_def bool_to_ternary_Unknown)




(*TODO: generic assumptions for a common matcher without information about IPs.
        to be used to add ipv6 integration without duplicating all proofs *)
definition matcher_generic :: "(common_primitive, simple_packet) exact_match_tac \<Rightarrow> bool" where
  "matcher_generic \<beta> \<equiv>
    (\<forall> p i. \<beta> (IIface i) p = bool_to_ternary (match_iface i (p_iiface p))) \<and>
    (\<forall> p i. \<beta> (OIface i) p = bool_to_ternary (match_iface i (p_oiface p))) \<and>
    (\<forall> p proto. \<beta> (Prot proto) p = bool_to_ternary (match_proto proto (p_proto p))) \<and>
    (\<forall> p ps. \<beta> (Src_Ports ps) p = bool_to_ternary (p_sport p \<in> ports_to_set ps)) \<and>
    (\<forall> p ps. \<beta> (Dst_Ports ps) p = bool_to_ternary (p_dport p \<in> ports_to_set ps)) \<and>
    (\<forall> p flags. \<beta> (L4_Flags flags) p = bool_to_ternary (match_tcp_flags flags (p_tcp_flags p))) \<and>
    (\<forall> p S. \<beta> (CT_State S) p = bool_to_ternary (match_ctstate S (p_tag_ctstate p))) \<and>
    (\<forall> p str. \<beta> (Extra str) p = TernaryUnknown)"

lemma matcher_generic_common_matcher: "matcher_generic common_matcher"
  by(simp add: matcher_generic_def)

end

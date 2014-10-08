theory IPSpace_Matcher
imports "../Semantics_Ternary" IPSpace_Syntax "../Bitmagic/IPv4Addr" "../Unknown_Match_Tacs"
begin




subsection{*Primitive Matchers: IP Space Matcher*}

(*for the first 4 cases, we set up better simp rules. this formulation is required such that simple_matcher is executable*)
fun simple_matcher :: "(iptrule_match, packet) exact_match_tac" where
  "simple_matcher (Src (Ip4Addr ip)) p = bool_to_ternary (ipv4addr_of_dotteddecimal ip = src_ip p)" |
  "simple_matcher (Src (Ip4AddrNetmask ip n)) p = bool_to_ternary (src_ip p \<in> ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal ip) n)" |
  "simple_matcher (Dst (Ip4Addr ip)) p = bool_to_ternary (ipv4addr_of_dotteddecimal ip = dst_ip p)" |
  "simple_matcher (Dst (Ip4AddrNetmask ip n)) p = bool_to_ternary (dst_ip p \<in> ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal ip) n)" |

  "simple_matcher (Prot ProtAll) _ = TernaryTrue" |
  "simple_matcher (Prot ipt_protocol.ProtTCP) p = bool_to_ternary (prot p = protPacket.ProtTCP)" |
  "simple_matcher (Prot ipt_protocol.ProtUDP) p = bool_to_ternary (prot p = protPacket.ProtUDP)" |

  "simple_matcher (Extra _) p = TernaryUnknown"


lemma simple_matcher_simps[simp]:
  "simple_matcher (Src ip) p = bool_to_ternary (src_ip p \<in> ipv4s_to_set ip)"
  "simple_matcher (Dst ip) p = bool_to_ternary (dst_ip p \<in> ipv4s_to_set ip)"
apply(case_tac [!] ip)
apply(auto)
apply (metis (poly_guards_query) bool_to_ternary_simps(2))+
done

declare simple_matcher.simps(1)[simp del]
declare simple_matcher.simps(2)[simp del]
declare simple_matcher.simps(3)[simp del]
declare simple_matcher.simps(4)[simp del]



text{*Perform very basic optimizations*}
fun opt_simple_matcher :: "iptrule_match match_expr \<Rightarrow> iptrule_match match_expr" where
  "opt_simple_matcher (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) = MatchAny" |
  "opt_simple_matcher (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) = MatchAny" |
  "opt_simple_matcher (Match (Prot ProtAll)) = MatchAny" |
  "opt_simple_matcher (Match m) = Match m" |
  "opt_simple_matcher (MatchNot m) = (MatchNot (opt_simple_matcher m))" |
  "opt_simple_matcher (MatchAnd m1 m2) = MatchAnd (opt_simple_matcher m1) (opt_simple_matcher m2)" |
  "opt_simple_matcher MatchAny = MatchAny"



lemma opt_simple_matcher_correct_matchexpr: "matches (simple_matcher, \<alpha>) m = matches (simple_matcher, \<alpha>) (opt_simple_matcher m)"
  apply(simp add: fun_eq_iff, clarify, rename_tac a p)
  apply(rule matches_iff_apply_f)
  apply(simp)
  apply(induction m rule: opt_simple_matcher.induct)
                              apply(simp_all add: eval_ternary_simps ip_in_ipv4range_set_from_bitmask_UNIV)
  done
corollary opt_simple_matcher_correct: "approximating_bigstep_fun (simple_matcher, \<alpha>) p (optimize_matches opt_simple_matcher rs) s = approximating_bigstep_fun (simple_matcher, \<alpha>) p rs s"
using optimize_matches opt_simple_matcher_correct_matchexpr by metis


text{*remove @{const Extra} (i.e. @{const TernaryUnknown}) match expressions*}
fun opt_simple_matcher_in_doubt_allow_extra :: "action \<Rightarrow> iptrule_match match_expr \<Rightarrow> iptrule_match match_expr" where
  "opt_simple_matcher_in_doubt_allow_extra _ MatchAny = MatchAny" |
  "opt_simple_matcher_in_doubt_allow_extra Accept (Match (Extra _)) = MatchAny" |
  "opt_simple_matcher_in_doubt_allow_extra Reject (Match (Extra _)) = MatchNot MatchAny" |
  "opt_simple_matcher_in_doubt_allow_extra Drop (Match (Extra _)) = MatchNot MatchAny" |
  "opt_simple_matcher_in_doubt_allow_extra _ (Match m) = Match m" |
  "opt_simple_matcher_in_doubt_allow_extra Accept (MatchNot (Match (Extra _))) = MatchAny" |
  "opt_simple_matcher_in_doubt_allow_extra Drop (MatchNot (Match (Extra _))) = MatchNot MatchAny" |
  "opt_simple_matcher_in_doubt_allow_extra Reject (MatchNot (Match (Extra _))) = MatchNot MatchAny" |
  "opt_simple_matcher_in_doubt_allow_extra a (MatchNot (MatchNot m)) = opt_simple_matcher_in_doubt_allow_extra a m" |

  --{*@{text "\<not> (a \<and> b) = \<not> b \<or> \<not> a"}   and   @{text "\<not> Unknown = Unknown"}*}
  "opt_simple_matcher_in_doubt_allow_extra a (MatchNot (MatchAnd m1 m2)) = 
    (if (opt_simple_matcher_in_doubt_allow_extra a (MatchNot m1)) = MatchAny \<or>
        (opt_simple_matcher_in_doubt_allow_extra a (MatchNot m2)) = MatchAny
        then MatchAny else 
        (if (opt_simple_matcher_in_doubt_allow_extra a (MatchNot m1)) = MatchNot MatchAny then 
          opt_simple_matcher_in_doubt_allow_extra a (MatchNot m2) else
         if (opt_simple_matcher_in_doubt_allow_extra a (MatchNot m2)) = MatchNot MatchAny then 
          opt_simple_matcher_in_doubt_allow_extra a (MatchNot m1) else
        MatchNot (MatchAnd m1 m2))
       )" |
  (* does not hold:
    "opt_simple_matcher_in_doubt_allow_extra a (MatchNot (MatchAnd m1 m2)) = 
    MatchNot (MatchAnd (opt_simple_matcher_in_doubt_allow_extra a m1) (opt_simple_matcher_in_doubt_allow_extra a m2))" |*)

  "opt_simple_matcher_in_doubt_allow_extra _ (MatchNot m) = MatchNot m" | (*TODO? But we already have MatchNot on all other cases*)
  "opt_simple_matcher_in_doubt_allow_extra a (MatchAnd m1 m2) = MatchAnd (opt_simple_matcher_in_doubt_allow_extra a m1) (opt_simple_matcher_in_doubt_allow_extra a m2)"


lemma[code_unfold]: "opt_simple_matcher_in_doubt_allow_extra a (MatchNot (MatchAnd m1 m2)) = 
    (let m1' = opt_simple_matcher_in_doubt_allow_extra a (MatchNot m1); m2' = opt_simple_matcher_in_doubt_allow_extra a (MatchNot m2) in
    (if m1' = MatchAny \<or> m2' = MatchAny
     then MatchAny
     else 
        if m1' = MatchNot MatchAny then m2' else
        if m2' = MatchNot MatchAny then m1'
     else
        MatchNot (MatchAnd m1 m2))
       )"
by(simp)


text{*
@{const opt_simple_matcher_in_doubt_allow_extra} can be expressed in terms of @{text remove_unknowns_generic}
*}
lemma assumes "a = Accept \<or> a = Drop" shows "opt_simple_matcher_in_doubt_allow_extra a m = remove_unknowns_generic (simple_matcher, in_doubt_allow) a m"
proof -
  {fix x1 x2 x3
  have 
    "(\<exists>p::packet. bool_to_ternary (src_ip p \<in> ipv4s_to_set x1) \<noteq> TernaryUnknown)"
    "(\<exists>p::packet. bool_to_ternary (dst_ip p \<in> ipv4s_to_set x2) \<noteq> TernaryUnknown)"
    "(\<exists>p::packet. simple_matcher (Prot x3) p \<noteq> TernaryUnknown)"
      apply -
      apply(simp_all add: bool_to_ternary_Unknown)
      apply(case_tac x3)
      apply(simp_all)
      apply(rule_tac x="\<lparr> src_ip = X, dst_ip = Y, prot = protPacket.ProtTCP \<rparr>" in exI, simp)
      apply(rule_tac x="\<lparr> src_ip = X, dst_ip = Y, prot = protPacket.ProtUDP \<rparr>" in exI, simp)
      done
  } note simple_matcher_packet_exists=this
  {fix \<gamma>
  have "a = Accept \<or> a = Drop \<Longrightarrow> \<gamma> = (simple_matcher, in_doubt_allow) \<Longrightarrow> opt_simple_matcher_in_doubt_allow_extra a m = remove_unknowns_generic \<gamma> a m"
    apply(induction \<gamma> a m rule: remove_unknowns_generic.induct)
      apply(simp_all)
      apply(case_tac [!] A)
      apply(case_tac [!] a)
      apply(simp_all)
      apply(simp_all add: simple_matcher_packet_exists)
      done
   } thus ?thesis using `a = Accept \<or> a = Drop` by simp
qed
    


(*TODO move?*)
lemma eval_ternary_And_UnknownTrue1: "eval_ternary_And TernaryUnknown t \<noteq> TernaryTrue"
apply(cases t)
apply(simp_all)
done



lemma "matches \<gamma> m1 a p = matches \<gamma> m2 a p \<Longrightarrow> matches \<gamma> (MatchNot m1) a p = matches \<gamma> (MatchNot m2) a p"
apply(case_tac \<gamma>)
apply(simp add: matches_case_ternaryvalue_tuple split: )
--{*counterexample:
  @{term m1} is unknown
  @{term m2} is true
  default matches
*}
oops

lemma opt_simple_matcher_in_doubt_allow_extra_correct_matchexpr: "matches (simple_matcher, in_doubt_allow) (opt_simple_matcher_in_doubt_allow_extra a m) a =
     matches (simple_matcher, in_doubt_allow) m a"
  apply(simp add: fun_eq_iff, clarify)
  apply(rename_tac p)
  apply(induction a m rule: opt_simple_matcher_in_doubt_allow_extra.induct)
                    apply(simp_all add: bunch_of_lemmata_about_matches matches_DeMorgan)
   apply(simp_all add: matches_case_ternaryvalue_tuple)
   
   apply safe
   apply(simp_all)
done

corollary opt_simple_matcher_in_doubt_allow_extra_correct: "approximating_bigstep_fun (simple_matcher, in_doubt_allow) p (optimize_matches_a opt_simple_matcher_in_doubt_allow_extra rs) s = approximating_bigstep_fun (simple_matcher, in_doubt_allow) p rs s"
using optimize_matches_a opt_simple_matcher_in_doubt_allow_extra_correct_matchexpr by metis


(*Same as above*)
fun opt_simple_matcher_in_doubt_deny_extra :: "action \<Rightarrow> iptrule_match match_expr \<Rightarrow> iptrule_match match_expr" where
  "opt_simple_matcher_in_doubt_deny_extra _ MatchAny = MatchAny" |
  "opt_simple_matcher_in_doubt_deny_extra Accept (Match (Extra _)) = MatchNot MatchAny" |
  "opt_simple_matcher_in_doubt_deny_extra Reject (Match (Extra _)) = MatchAny" |
  "opt_simple_matcher_in_doubt_deny_extra Drop (Match (Extra _)) = MatchAny" |
  "opt_simple_matcher_in_doubt_deny_extra _ (Match m) = Match m" |
  "opt_simple_matcher_in_doubt_deny_extra Reject (MatchNot (Match (Extra _))) = MatchAny" |
  "opt_simple_matcher_in_doubt_deny_extra Drop (MatchNot (Match (Extra _))) = MatchAny" |
  "opt_simple_matcher_in_doubt_deny_extra Accept (MatchNot (Match (Extra _))) = MatchNot MatchAny" |
  "opt_simple_matcher_in_doubt_deny_extra a (MatchNot (MatchNot m)) = opt_simple_matcher_in_doubt_deny_extra a m" |

  (*\<not> (a \<and> b) = \<not> b \<or> \<not> a   and   \<not> Unknown = Unknown*)
  "opt_simple_matcher_in_doubt_deny_extra a (MatchNot (MatchAnd m1 m2)) = 
    (if (opt_simple_matcher_in_doubt_deny_extra a (MatchNot m1)) = MatchAny \<or>
        (opt_simple_matcher_in_doubt_deny_extra a (MatchNot m2)) = MatchAny
        then MatchAny else 
        (if (opt_simple_matcher_in_doubt_deny_extra a (MatchNot m1)) = MatchNot MatchAny then 
          opt_simple_matcher_in_doubt_deny_extra a (MatchNot m2) else
         if (opt_simple_matcher_in_doubt_deny_extra a (MatchNot m2)) = MatchNot MatchAny then 
          opt_simple_matcher_in_doubt_deny_extra a (MatchNot m1) else
        MatchNot (MatchAnd m1 m2))
       )" |
  "opt_simple_matcher_in_doubt_deny_extra _ (MatchNot m) = MatchNot m" | (*TODO*)
  "opt_simple_matcher_in_doubt_deny_extra a (MatchAnd m1 m2) = MatchAnd (opt_simple_matcher_in_doubt_deny_extra a m1) (opt_simple_matcher_in_doubt_deny_extra a m2)"


lemma opt_simple_matcher_in_doubt_deny_extra_correct_matchexpr: "matches (simple_matcher, in_doubt_deny) (opt_simple_matcher_in_doubt_deny_extra a m) a = matches (simple_matcher, in_doubt_deny) m a"
  apply(simp add: fun_eq_iff, clarify)
  apply(rename_tac p)
  apply(induction a m rule: opt_simple_matcher_in_doubt_deny_extra.induct)
                    apply(simp_all add: bunch_of_lemmata_about_matches matches_DeMorgan)
   apply(simp_all add: matches_case_ternaryvalue_tuple)
   
   apply safe
   apply(simp_all)
done
(*
  apply(induction a m rule: opt_simple_matcher_in_doubt_deny_extra.induct)
                      apply(simp_all add: bunch_of_lemmata_about_matches)
   apply(simp_all add: matches_case_ternaryvalue_tuple)
done*)
corollary opt_simple_matcher_in_doubt_deny_extra_correct: "approximating_bigstep_fun (simple_matcher, in_doubt_deny) p (optimize_matches_a opt_simple_matcher_in_doubt_deny_extra rs) s = approximating_bigstep_fun (simple_matcher, in_doubt_deny) p rs s"
using optimize_matches_a opt_simple_matcher_in_doubt_deny_extra_correct_matchexpr by metis






text{*Lemmas when matching on @{term Src} or @{term Dst}*}
lemma simple_matcher_SrcDst_defined: "simple_matcher (Src m) p \<noteq> TernaryUnknown" "simple_matcher (Dst m) p \<noteq> TernaryUnknown"
  apply(case_tac [!] m)
  apply(simp_all add: bool_to_ternary_Unknown)
  done
lemma simple_matcher_SrcDst_defined_simp:
  "simple_matcher (Src x) p \<noteq> TernaryFalse \<longleftrightarrow> simple_matcher (Src x) p = TernaryTrue"
  "simple_matcher (Dst x) p \<noteq> TernaryFalse \<longleftrightarrow> simple_matcher (Dst x) p = TernaryTrue"
apply (metis eval_ternary_Not.cases simple_matcher_SrcDst_defined(1) ternaryvalue.distinct(1))
apply (metis eval_ternary_Not.cases simple_matcher_SrcDst_defined(2) ternaryvalue.distinct(1))
done
lemma match_simplematcher_SrcDst:
  "matches (simple_matcher, \<alpha>) (Match (Src X)) a p \<longleftrightarrow> src_ip  p \<in> ipv4s_to_set X"
  "matches (simple_matcher, \<alpha>) (Match (Dst X)) a p \<longleftrightarrow> dst_ip  p \<in> ipv4s_to_set X"
   apply(simp_all add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)
   apply (metis bool_to_ternary.elims bool_to_ternary_Unknown ternaryvalue.distinct(1))+
   done
lemma match_simplematcher_SrcDst_not:
  "matches (simple_matcher, \<alpha>) (MatchNot (Match (Src X))) a p \<longleftrightarrow> src_ip  p \<notin> ipv4s_to_set X"
  "matches (simple_matcher, \<alpha>) (MatchNot (Match (Dst X))) a p \<longleftrightarrow> dst_ip  p \<notin> ipv4s_to_set X"
   apply(simp_all add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)
   apply(case_tac [!] X)
   apply(simp_all add: bool_to_ternary_simps)
   done
lemma simple_matcher_SrcDst_Inter:
  "(\<forall>m\<in>set X. matches (simple_matcher, \<alpha>) (Match (Src m)) a p) \<longleftrightarrow> src_ip p \<in> (\<Inter>x\<in>set X. ipv4s_to_set x)"
  "(\<forall>m\<in>set X. matches (simple_matcher, \<alpha>) (Match (Dst m)) a p) \<longleftrightarrow> dst_ip p \<in> (\<Inter>x\<in>set X. ipv4s_to_set x)"
  apply(simp_all)
  apply(simp_all add: matches_case_ternaryvalue_tuple bool_to_ternary_Unknown bool_to_ternary_simps split: ternaryvalue.split)
 done

end

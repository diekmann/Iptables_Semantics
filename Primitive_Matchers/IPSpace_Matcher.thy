theory IPSpace_Matcher
imports "../Semantics_Ternary" IPSpace_Syntax "../Bitmagic/IPv4Addr" "../Unknown_Match_Tacs"
begin




subsection{*Primitive Matchers: IP Space Matcher*}

(*for the first 4 cases, we set up better simp rules. this formulation is required such that simple_matcher is executable*)
fun simple_matcher :: "(iptrule_match, packet) exact_match_tac" where
  "simple_matcher (Src (Ip4Addr ip)) p = bool_to_ternary (ipv4addr_of_dotdecimal ip = src_ip p)" |
  "simple_matcher (Src (Ip4AddrNetmask ip n)) p = bool_to_ternary (src_ip p \<in> ipv4range_set_from_bitmask (ipv4addr_of_dotdecimal ip) n)" |
  "simple_matcher (Dst (Ip4Addr ip)) p = bool_to_ternary (ipv4addr_of_dotdecimal ip = dst_ip p)" |
  "simple_matcher (Dst (Ip4AddrNetmask ip n)) p = bool_to_ternary (dst_ip p \<in> ipv4range_set_from_bitmask (ipv4addr_of_dotdecimal ip) n)" |

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
fun upper_closure_matchexpr :: "action \<Rightarrow> iptrule_match match_expr \<Rightarrow> iptrule_match match_expr" where
  "upper_closure_matchexpr _ MatchAny = MatchAny" |
  "upper_closure_matchexpr Accept (Match (Extra _)) = MatchAny" |
  "upper_closure_matchexpr Reject (Match (Extra _)) = MatchNot MatchAny" |
  "upper_closure_matchexpr Drop (Match (Extra _)) = MatchNot MatchAny" |
  "upper_closure_matchexpr _ (Match m) = Match m" |
  "upper_closure_matchexpr Accept (MatchNot (Match (Extra _))) = MatchAny" |
  "upper_closure_matchexpr Drop (MatchNot (Match (Extra _))) = MatchNot MatchAny" |
  "upper_closure_matchexpr Reject (MatchNot (Match (Extra _))) = MatchNot MatchAny" |
  "upper_closure_matchexpr a (MatchNot (MatchNot m)) = upper_closure_matchexpr a m" |

  --{*@{text "\<not> (a \<and> b) = \<not> b \<or> \<not> a"}   and   @{text "\<not> Unknown = Unknown"}*}
  "upper_closure_matchexpr a (MatchNot (MatchAnd m1 m2)) = 
    (if (upper_closure_matchexpr a (MatchNot m1)) = MatchAny \<or>
        (upper_closure_matchexpr a (MatchNot m2)) = MatchAny
        then MatchAny else 
        (if (upper_closure_matchexpr a (MatchNot m1)) = MatchNot MatchAny then 
          upper_closure_matchexpr a (MatchNot m2) else
         if (upper_closure_matchexpr a (MatchNot m2)) = MatchNot MatchAny then 
          upper_closure_matchexpr a (MatchNot m1) else
        MatchNot (MatchAnd (MatchNot (upper_closure_matchexpr a (MatchNot m1))) (MatchNot (upper_closure_matchexpr a (MatchNot m2)))))
       )" |
       --{*For the final else case, we exploit idempotence of not to introduce recursive calls*}
  (* does not hold:
    "upper_closure_matchexpr a (MatchNot (MatchAnd m1 m2)) = 
    MatchNot (MatchAnd (upper_closure_matchexpr a m1) (upper_closure_matchexpr a m2))" |*)

  "upper_closure_matchexpr _ (MatchNot m) = MatchNot m" | (*TODO? But we already have MatchNot on all other cases*)
  "upper_closure_matchexpr a (MatchAnd m1 m2) = MatchAnd (upper_closure_matchexpr a m1) (upper_closure_matchexpr a m2)"


lemma[code_unfold]: "upper_closure_matchexpr a (MatchNot (MatchAnd m1 m2)) = 
    (let m1' = upper_closure_matchexpr a (MatchNot m1); m2' = upper_closure_matchexpr a (MatchNot m2) in
    (if m1' = MatchAny \<or> m2' = MatchAny
     then MatchAny
     else 
        if m1' = MatchNot MatchAny then m2' else
        if m2' = MatchNot MatchAny then m1'
     else
        MatchNot (MatchAnd (MatchNot m1') (MatchNot m2')))
       )"
by(simp)


text{*
@{const upper_closure_matchexpr} can be expressed in terms of @{const remove_unknowns_generic}
*}
lemma assumes "a = Accept \<or> a = Drop" shows "upper_closure_matchexpr a m = remove_unknowns_generic (simple_matcher, in_doubt_allow) a m"
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
  have "a = Accept \<or> a = Drop \<Longrightarrow> \<gamma> = (simple_matcher, in_doubt_allow) \<Longrightarrow> upper_closure_matchexpr a m = remove_unknowns_generic \<gamma> a m"
    apply(induction \<gamma> a m rule: remove_unknowns_generic.induct)
      apply(simp_all)
      apply(case_tac [!] A)
      apply(case_tac [!] a)
      apply(simp_all)
      apply(simp_all add: unknown_match_all_def unknown_not_match_any_def simple_matcher_packet_exists)
      done
   } thus ?thesis using `a = Accept \<or> a = Drop` by simp
qed



fun has_unknowns :: " ('a, 'p) exact_match_tac \<Rightarrow> 'a match_expr \<Rightarrow> bool" where
  "has_unknowns \<beta> (Match A) = (\<exists>p. ternary_ternary_eval (map_match_tac \<beta> p (Match A)) = TernaryUnknown)" |
  "has_unknowns \<beta> (MatchNot m) = has_unknowns \<beta> m" |
  "has_unknowns \<beta> MatchAny = False" |
  "has_unknowns \<beta> (MatchAnd m1 m2) = (has_unknowns \<beta> m1 \<or> has_unknowns \<beta> m2)"

(*
lemma "has_unknowns \<beta> = has_disc"*)

lemma simple_matcher_prot_not_unkown: "simple_matcher (Prot v) p \<noteq> TernaryUnknown"
  apply(cases v)
  apply(simp_all add: bool_to_ternary_Unknown)
done

text{*@{const upper_closure_matchexpr} does indeed remove all unknowns*}
theorem upper_closure_matchexpr_specification:
  "a = Accept \<or> a = Drop \<or> a = Reject \<Longrightarrow> \<not> has_unknowns simple_matcher (upper_closure_matchexpr a m)"
  apply(induction a m rule: upper_closure_matchexpr.induct)
  apply(simp_all add: bool_to_ternary_Unknown simple_matcher_prot_not_unkown)
done

value "upper_closure_matchexpr Drop (MatchNot (MatchAnd (MatchNot MatchAny) (MatchNot (MatchAnd (MatchNot MatchAny) (Match (Extra ''foo''))))))"
value "upper_closure_matchexpr Accept ((MatchAnd (MatchNot MatchAny) (MatchNot (MatchAnd (MatchNot MatchAny) (Match (Extra ''foo''))))))"

(*
lemma "(\<exists>p. ternary_ternary_eval (map_match_tac \<beta> p m) = TernaryUnknown) \<Longrightarrow> has_unknowns \<beta> m"
apply(clarify)
apply(induction m)
apply(simp_all)
apply(rule_tac x=p in exI, simp)
apply (metis eval_ternary_Not_UnknownD)
by (metis (poly_guards_query) eval_ternary_simps(2) eval_ternary_simps(4) ternaryvalue.exhaust)


lemma a_unknown_extraD: "\<exists>p. simple_matcher (a::iptrule_match) p = TernaryUnknown \<Longrightarrow> \<exists>X. a = Extra X"
  apply(clarify)
  apply(case_tac a)
  apply(simp_all add: bool_to_ternary_Unknown)
  using simple_matcher_prot_not_unkown by blast

lemma has_unknowns_simple_matcher_base: "has_unknowns simple_matcher (Match A) \<longleftrightarrow> (\<exists>X. A = Extra X)"
  apply(simp)
  apply(rule iffI)
   apply(drule a_unknown_extraD, simp)
  by auto


fun has_unknowns_simple_matcher :: "(iptrule_match, packet) exact_match_tac \<Rightarrow> iptrule_match match_expr \<Rightarrow> bool" where
  "has_unknowns_simple_matcher \<beta> (Match A) = (\<exists>X. A = Extra X)" |
  "has_unknowns_simple_matcher \<beta> (MatchNot m) = has_unknowns \<beta> m" |
  "has_unknowns_simple_matcher \<beta> MatchAny = False" |
  "has_unknowns_simple_matcher \<beta> (MatchAnd m1 m2) = (has_unknowns_simple_matcher \<beta> m1 \<or> has_unknowns_simple_matcher \<beta> m2)"

value "upper_closure_matchexpr Drop
    (MatchNot (MatchAnd 
      (MatchAnd (Match (Src (Ip4Addr (0,0,0,0)))) MatchAny)
      (MatchNot (MatchAnd (MatchNot MatchAny) (Match (Extra ''foo''))))))"
  

lemma "has_unknowns simple_matcher m \<Longrightarrow>
    (upper_closure_matchexpr a (MatchNot m) \<noteq> MatchAny) \<or>
    (upper_closure_matchexpr a (MatchNot m) \<noteq> MatchNot MatchAny)"
by (metis match_expr.distinct(9))



lemma matchexpr_neq_matchnot_n_matchany: "\<forall>n. m \<noteq> (MatchNot^^n) MatchAny \<Longrightarrow>  (\<exists>A n. m = (MatchNot^^n) (Match A)) \<or> (\<exists> m1 m2 n. m = (MatchNot^^n) (MatchAnd m1 m2))"
  apply(induction m)
apply (metis funpow.simps(1) id_apply)
apply (metis comp_apply funpow.simps(2))
apply (metis funpow.simps(1) id_apply)
apply (metis funpow.simps(1) id_apply)
done
lemma matexp_neq_matchany1: "Match X \<noteq> (MatchNot ^^ n) MatchAny"
  by(induction n) (simp_all)
lemma matexp_neq_matchany2: "MatchNot (Match X) \<noteq> (MatchNot ^^ n) MatchAny"
  by(induction n) (simp_all add: matexp_neq_matchany1)
lemma matexp_neq_matchany3: "MatchAnd m1 m2 \<noteq> (MatchNot ^^ n) MatchAny"
  by(induction n) (simp_all)
lemma matexp_neq_matchany4: "MatchNot (MatchAnd m1 m2) \<noteq> (MatchNot ^^ n) MatchAny"
  by(induction n) (simp_all add: matexp_neq_matchany3)
lemma matexp_neq_matchany5: "MatchAny \<noteq> (MatchNot ^^ n) (Match A)"
  by(induction n) (simp_all)
lemma matexp_neq_matchany6: "MatchNot MatchAny \<noteq> (MatchNot ^^ n) (Match A)"
  by(induction n) (simp_all add: matexp_neq_matchany5)
  
lemma upper_closure_matchexpr_matchexpr_neq_matchnot_n_matchany:
      "upper_closure_matchexpr a (MatchNot m) \<noteq> MatchNot MatchAny \<Longrightarrow>
       upper_closure_matchexpr a (MatchNot m) \<noteq> MatchAny \<Longrightarrow>
       \<forall>n. upper_closure_matchexpr a (MatchNot m) \<noteq> (MatchNot^^n) MatchAny"
  apply(induction a m rule: upper_closure_matchexpr.induct)
  apply(simp_all add: matexp_neq_matchany1 matexp_neq_matchany2 matexp_neq_matchany3 matexp_neq_matchany4)
  apply(safe)
  apply presburger+
  done

(*
lemma "upper_closure_matchexpr Accept (MatchNot m) = MatchNot MatchAny \<Longrightarrow>
    (\<exists>n. m = (MatchNot ^^ n) MatchAny) \<or> (\<exists> m1 m2 n. m = (MatchNot^^n) (MatchAnd m1 m2))"
  apply(induction Accept m arbitrary: rule: upper_closure_matchexpr.induct)
  apply(simp_all add: bool_to_ternary_Unknown simple_matcher_prot_not_unkown)
  apply(rule disjI1)
  apply(rule_tac x=0 in exI,simp)
  apply(erule disjE)
  apply(clarify)
  apply(rule_tac x="Suc (Suc n)" in exI,simp)
  apply(erule exE)+
  apply(simp)
  apply(rule disjI2)
  apply(rule_tac x=m1 in exI)
  apply(rule_tac x=m2 in exI)
  apply(rule_tac x="Suc (Suc n)" in exI)
  apply(simp)
  apply(simp split: split_if_asm)
  apply(erule disjE)
  apply(erule exE)+
  apply(erule disjE)
  apply(erule exE)+
  apply simp
  apply(rule disjI2)
  apply(rule_tac x=m1 in exI)
  apply(rule_tac x=m2 in exI)
  apply(rule_tac x=0 in exI)
  apply simp
  apply(rule disjI2)
  apply(rule_tac x=m1 in exI)
  apply(rule_tac x=m2 in exI)
  apply(rule_tac x=0 in exI)
  apply simp
  apply(rule disjI2)
  apply(rule_tac x=m1 in exI)
  apply(rule_tac x=m2 in exI)
  apply(rule_tac x=0 in exI)
  apply simp
  done
*)
lemma not_has_unknowns_simplematcher_1: "\<not> has_unknowns simple_matcher ((MatchNot ^^ n) MatchAny)"
  by(induction n) (simp_all)
lemma not_has_unknowns_simplematcher_2: "\<not> has_unknowns simple_matcher m1 \<Longrightarrow>
       \<not> has_unknowns simple_matcher m2 \<Longrightarrow>
       \<not> has_unknowns simple_matcher ((MatchNot ^^ n) (MatchAnd m1 m2))"
  by(induction n) (simp_all)
lemma upper_closure_matchexpr_Accept_MatchNot_MatchNotMatchAny: 
  "upper_closure_matchexpr Accept (MatchNot m) = MatchNot MatchAny \<Longrightarrow>
    (\<exists>n. m = (MatchNot ^^ n) MatchAny) \<or> (\<exists> m1 m2 n. (m = (MatchNot^^n) (MatchAnd m1 m2)) \<and> \<not> has_unknowns simple_matcher m1 \<and> \<not> has_unknowns simple_matcher m2)"
  apply(induction Accept m arbitrary: rule: upper_closure_matchexpr.induct)
  apply(simp_all add: bool_to_ternary_Unknown simple_matcher_prot_not_unkown)
  apply(rule disjI1)
  apply(rule_tac x=0 in exI,simp)
  apply(erule disjE)
  apply(clarify)
  apply(rule_tac x="Suc (Suc n)" in exI,simp)
  apply(elim exE conjE)+
  apply(simp)
  apply(rule disjI2)
  apply(rule_tac x=m1 in exI, simp)
  apply(rule_tac x=m2 in exI, simp)
  apply(rule_tac x="Suc (Suc n)" in exI)
  apply(simp)
  apply(simp split: split_if_asm)
  apply(erule disjE)
  apply(erule exE)+
  apply(erule disjE)
  apply(erule exE)+
  apply simp
  apply(rule disjI2)
  apply(rule_tac x=m1 in exI, simp add: not_has_unknowns_simplematcher_1)
  apply(rule_tac x=m2 in exI, simp add: not_has_unknowns_simplematcher_1)
  apply(rule_tac x=0 in exI)
  apply simp
  apply(rule disjI2)
  apply(elim disjE conjE exE)
  apply(rule_tac x=m1 in exI, simp add: not_has_unknowns_simplematcher_1)
  apply(rule_tac x=m2 in exI, simp add: not_has_unknowns_simplematcher_1 not_has_unknowns_simplematcher_2)
  apply(rule_tac x=0 in exI)
  apply simp
  apply(rule disjI2)
  apply(elim disjE conjE exE)
  apply(simp)
  apply(rule_tac x=m1 in exI)
  apply(simp add: not_has_unknowns_simplematcher_1)
  apply(rule_tac x=m2 in exI)
  apply(simp add: not_has_unknowns_simplematcher_1 not_has_unknowns_simplematcher_2)
  apply(rule_tac x=0 in exI)
  apply simp
  apply(rule_tac x=m1 in exI)
  apply(simp add: not_has_unknowns_simplematcher_1)
  apply(rule_tac x=m2 in exI)
  apply(simp add: not_has_unknowns_simplematcher_1 not_has_unknowns_simplematcher_2)
  apply(rule_tac x=0 in exI)
  apply simp
  done
lemma "a = Accept (*\<or> a = Drop \<or> a = Reject*) \<Longrightarrow> upper_closure_matchexpr a ( m) = ( (Match A)) \<Longrightarrow> \<not> has_unknowns simple_matcher m"
  apply(induction a m arbitrary: rule: upper_closure_matchexpr.induct)
  apply(simp_all add: bool_to_ternary_Unknown simple_matcher_prot_not_unkown)
  apply(auto dest: a_unknown_extraD simp: bool_to_ternary_Unknown simple_matcher_prot_not_unkown)[3]
  apply(thin_tac "?x \<Longrightarrow> ?y \<Longrightarrow> True")+
  apply(thin_tac "?x \<Longrightarrow> ?y \<Longrightarrow> ?z \<Longrightarrow> True")+
  apply(simp split: split_if_asm)
  apply(thin_tac "False \<Longrightarrow> ?x")
  apply(drule upper_closure_matchexpr_Accept_MatchNot_MatchNotMatchAny)
  apply(elim disjE exE)
  apply(simp_all add: not_has_unknowns_simplematcher_1 not_has_unknowns_simplematcher_2)
  apply(thin_tac "False \<Longrightarrow> ?x")
  apply(drule upper_closure_matchexpr_Accept_MatchNot_MatchNotMatchAny)
  apply(elim disjE exE)
  apply(simp_all add: not_has_unknowns_simplematcher_1 not_has_unknowns_simplematcher_2)
done

  (*TODO: show this one!!*)
lemma "a = Accept \<or> a = Drop \<or> a = Reject \<Longrightarrow> \<not> has_unknowns simple_matcher (upper_closure_matchexpr a m)"
  apply(induction a m rule: upper_closure_matchexpr.induct)
  apply(simp_all add: bool_to_ternary_Unknown simple_matcher_prot_not_unkown)[22]
  defer
  apply(simp_all add: bool_to_ternary_Unknown simple_matcher_prot_not_unkown)[23]
  apply(simp_all add: bool_to_ternary_Unknown simple_matcher_prot_not_unkown)
  apply clarify
  apply simp
  apply(thin_tac "False \<Longrightarrow> True")+

  apply(drule(1) upper_closure_matchexpr_matchexpr_neq_matchnot_n_matchany)
  apply(drule matchexpr_neq_matchnot_n_matchany)
  apply(drule(1) upper_closure_matchexpr_matchexpr_neq_matchnot_n_matchany)
  apply(drule matchexpr_neq_matchnot_n_matchany)
  apply(erule disjE)
  back (*WAHHHHHH*)
  apply(erule disjE)
  back (*WAHHHHHH*)
  apply(clarify)

  apply(rule conjI)
  thm match_expr.induct
  apply(rule match_expr.induct)
  apply(simp_all add: has_unknowns_simple_matcher_base del: has_unknowns.simps(1))
oops
*)

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

lemma upper_closure_matchexpr_correct_matchexpr: "matches (simple_matcher, in_doubt_allow) (upper_closure_matchexpr a m) a =
     matches (simple_matcher, in_doubt_allow) m a"
  apply(simp add: fun_eq_iff, clarify)
  apply(rename_tac p)
  apply(induction a m rule: upper_closure_matchexpr.induct)
                    apply(simp_all add: bunch_of_lemmata_about_matches matches_DeMorgan)
   apply(simp_all add: matches_case_ternaryvalue_tuple)
   
   apply safe
   apply(simp_all)
done

corollary upper_closure_matchexpr_correct:
  "approximating_bigstep_fun (simple_matcher, in_doubt_allow) p (optimize_matches_a upper_closure_matchexpr rs) s = 
   approximating_bigstep_fun (simple_matcher, in_doubt_allow) p rs s"
using optimize_matches_a upper_closure_matchexpr_correct_matchexpr by metis


(*Same as above*)
fun lower_closure_matchexpr :: "action \<Rightarrow> iptrule_match match_expr \<Rightarrow> iptrule_match match_expr" where
  "lower_closure_matchexpr _ MatchAny = MatchAny" |
  "lower_closure_matchexpr Accept (Match (Extra _)) = MatchNot MatchAny" |
  "lower_closure_matchexpr Reject (Match (Extra _)) = MatchAny" |
  "lower_closure_matchexpr Drop (Match (Extra _)) = MatchAny" |
  "lower_closure_matchexpr _ (Match m) = Match m" |
  "lower_closure_matchexpr Reject (MatchNot (Match (Extra _))) = MatchAny" |
  "lower_closure_matchexpr Drop (MatchNot (Match (Extra _))) = MatchAny" |
  "lower_closure_matchexpr Accept (MatchNot (Match (Extra _))) = MatchNot MatchAny" |
  "lower_closure_matchexpr a (MatchNot (MatchNot m)) = lower_closure_matchexpr a m" |

  (*\<not> (a \<and> b) = \<not> b \<or> \<not> a   and   \<not> Unknown = Unknown*)
  "lower_closure_matchexpr a (MatchNot (MatchAnd m1 m2)) = 
    (if (lower_closure_matchexpr a (MatchNot m1)) = MatchAny \<or>
        (lower_closure_matchexpr a (MatchNot m2)) = MatchAny
        then MatchAny else 
        (if (lower_closure_matchexpr a (MatchNot m1)) = MatchNot MatchAny then 
          lower_closure_matchexpr a (MatchNot m2) else
         if (lower_closure_matchexpr a (MatchNot m2)) = MatchNot MatchAny then 
          lower_closure_matchexpr a (MatchNot m1) else
        MatchNot (MatchAnd (MatchNot (lower_closure_matchexpr a (MatchNot m1))) (MatchNot (lower_closure_matchexpr a (MatchNot m2)))))
       )" |
  "lower_closure_matchexpr _ (MatchNot m) = MatchNot m" | (*TODO*)
  "lower_closure_matchexpr a (MatchAnd m1 m2) = MatchAnd (lower_closure_matchexpr a m1) (lower_closure_matchexpr a m2)"


lemma lower_closure_matchexpr_correct_matchexpr: "matches (simple_matcher, in_doubt_deny) (lower_closure_matchexpr a m) a = matches (simple_matcher, in_doubt_deny) m a"
  apply(simp add: fun_eq_iff, clarify)
  apply(rename_tac p)
  apply(induction a m rule: lower_closure_matchexpr.induct)
                    apply(simp_all add: bunch_of_lemmata_about_matches matches_DeMorgan)
   apply(simp_all add: matches_case_ternaryvalue_tuple)
   
   apply safe
   apply(simp_all)
done
(*
  apply(induction a m rule: lower_closure_matchexpr.induct)
                      apply(simp_all add: bunch_of_lemmata_about_matches)
   apply(simp_all add: matches_case_ternaryvalue_tuple)
done*)
corollary lower_closure_matchexpr_correct: "approximating_bigstep_fun (simple_matcher, in_doubt_deny) p (optimize_matches_a lower_closure_matchexpr rs) s = approximating_bigstep_fun (simple_matcher, in_doubt_deny) p rs s"
using optimize_matches_a lower_closure_matchexpr_correct_matchexpr by metis



theorem lower_closure_matchexpr_specification:
  "a = Accept \<or> a = Drop \<or> a = Reject \<Longrightarrow> \<not> has_unknowns simple_matcher (lower_closure_matchexpr a m)"
  apply(induction a m rule: lower_closure_matchexpr.induct)
  apply(simp_all add: bool_to_ternary_Unknown simple_matcher_prot_not_unkown)
done



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

theory Format_Ln
imports "../Fixed_Action" Negation_Type "../Bitmagic/Numberwang_Ln" IPSpace_Syntax "../Bitmagic/IPv4Addr" "../Packet_Set"
begin


section{*iptables LN formatting*}
text{*
Produce output as produced by the command: iptables -L -n
*}

text{*Example*}
text_raw{*
\begin{verbatim}
Chain INPUT (policy ACCEPT)
target     prot opt source               destination
STATEFUL   all  --  0.0.0.0/0            0.0.0.0/0
ACCEPT     all  --  0.0.0.0/0            0.0.0.0/0
ACCEPT     icmp --  0.0.0.0/0            0.0.0.0/0            icmptype 3
...
\end{verbatim}
*}


(*TODO: this is the thing I want*)
datatype iptrule_match_Ln = FormattedMatch (*Src*) "ipt_ipv4range negation_type" (*Dst*) "ipt_ipv4range negation_type" (*Prot*) "ipt_protocol negation_type" (*Extra*) "string negation_type list"

(*this is the thing we have at the moment. Todo: compress the lists to one entry*)
datatype iptrule_match_Ln_uncompressed = UncompressedFormattedMatch 
  (*Src*) "ipt_ipv4range negation_type list"
  (*Dst*) "ipt_ipv4range negation_type list"
  (*Prot*) "ipt_protocol negation_type list"
  (*Extra*) "string negation_type list"



fun srclist_and :: "ipt_ipv4range negation_type list\<Rightarrow> iptrule_match match_expr" where
  "srclist_and [] = MatchAny" |
  "srclist_and ((Pos e)#es) = MatchAnd (Match (Src e)) (srclist_and es)" |
  "srclist_and ((Neg e)#es) = MatchAnd (MatchNot (Match (Src e))) (srclist_and es)"

fun dstlist_and :: "ipt_ipv4range negation_type list\<Rightarrow> iptrule_match match_expr" where
  "dstlist_and [] = MatchAny" |
  "dstlist_and ((Pos e)#es) = MatchAnd (Match (Dst e)) (dstlist_and es)" |
  "dstlist_and ((Neg e)#es) = MatchAnd (MatchNot (Match (Dst e))) (dstlist_and es)"

fun protolist_and :: "ipt_protocol negation_type list\<Rightarrow> iptrule_match match_expr" where
  "protolist_and [] = MatchAny" |
  "protolist_and ((Pos e)#es) = MatchAnd (Match (Prot e)) (protolist_and es)" |
  "protolist_and ((Neg e)#es) = MatchAnd (MatchNot (Match (Prot e))) (protolist_and es)"

fun extralist_and :: "string negation_type list\<Rightarrow> iptrule_match match_expr" where
  "extralist_and [] = MatchAny" |
  "extralist_and ((Pos e)#es) = MatchAnd (Match (Extra e)) (extralist_and es)" |
  "extralist_and ((Neg e)#es) = MatchAnd (MatchNot (Match (Extra e))) (extralist_and es)"

text{*We can express all those @{term srclist_and} functions and similar in a simpler fashion!*}
fun alist_and :: "'a negation_type list \<Rightarrow> 'a match_expr" where
  "alist_and [] = MatchAny" |
  "alist_and ((Pos e)#es) = MatchAnd (Match e) (alist_and es)" |
  "alist_and ((Neg e)#es) = MatchAnd (MatchNot (Match e)) (alist_and es)"

lemma list_and_simps1: "srclist_and es = alist_and (NegPos_map Src es)"
  by(induction es rule: alist_and.induct)(simp_all)
lemma list_and_simps2: "dstlist_and es = alist_and (NegPos_map Dst es)"
  by(induction es rule: alist_and.induct)(simp_all)
lemma list_and_simps3: "protolist_and es = alist_and (NegPos_map Prot es)"
  by(induction es rule: alist_and.induct)(simp_all)
lemma list_and_simps4: "extralist_and es = alist_and (NegPos_map Extra es)"
  by(induction es rule: alist_and.induct)(simp_all)


fun UncompressedFormattedMatch_to_match_expr :: "iptrule_match_Ln_uncompressed \<Rightarrow> iptrule_match match_expr" where
  "UncompressedFormattedMatch_to_match_expr (UncompressedFormattedMatch src dst proto extra) = 
    MatchAnd (srclist_and src) (MatchAnd (dstlist_and dst) (MatchAnd (protolist_and proto) (extralist_and extra)))"


fun FormattedMatch_to_match_expr :: "iptrule_match_Ln \<Rightarrow> iptrule_match match_expr" where
  "FormattedMatch_to_match_expr (FormattedMatch src dst proto extra) = MatchAnd 
    (case src of Pos s \<Rightarrow> Match (Src s) | Neg s \<Rightarrow> MatchNot (Match (Src s)))
    (MatchAnd
      (case dst of Pos d \<Rightarrow> Match (Dst d) | Neg d \<Rightarrow> MatchNot (Match (Dst d)))
      (MatchAnd
         (case proto of Pos p \<Rightarrow> Match (Prot p) | Neg p \<Rightarrow> MatchNot (Match (Prot p)))
         (extralist_and extra)
      )
    )"

fun iptrule_match_Ln_uncompressed_append :: "iptrule_match_Ln_uncompressed \<Rightarrow> iptrule_match_Ln_uncompressed \<Rightarrow> iptrule_match_Ln_uncompressed" where
  "iptrule_match_Ln_uncompressed_append (UncompressedFormattedMatch src1 dst1 proto1 extra1) (UncompressedFormattedMatch src2 dst2 proto2 extra2) = 
        UncompressedFormattedMatch (src1@src2) (dst1@dst2) (proto1@proto2) (extra1@extra2)"

text{* assumes: @{const "normalized_match"}*}
fun iptrule_match_collect :: "iptrule_match match_expr \<Rightarrow> iptrule_match_Ln_uncompressed \<Rightarrow> iptrule_match_Ln_uncompressed" where
  "iptrule_match_collect MatchAny accu = accu" |
  "iptrule_match_collect (Match (Src ip)) (UncompressedFormattedMatch src dst proto extra) = UncompressedFormattedMatch ((Pos ip)#src) dst proto extra" |
  "iptrule_match_collect (Match (Dst ip)) (UncompressedFormattedMatch src dst proto extra) = UncompressedFormattedMatch src ((Pos ip)#dst) proto extra" |
  "iptrule_match_collect (Match (Prot p)) (UncompressedFormattedMatch src dst proto extra) = UncompressedFormattedMatch src dst ((Pos p)#proto) extra"  |
  "iptrule_match_collect (Match (Extra e)) (UncompressedFormattedMatch src dst proto extra) = UncompressedFormattedMatch src dst proto ((Pos e)#extra)" |
  "iptrule_match_collect (MatchNot (Match (Src ip))) (UncompressedFormattedMatch src dst proto extra) = UncompressedFormattedMatch ((Neg ip)#src) dst proto extra" |
  "iptrule_match_collect (MatchNot (Match (Dst ip))) (UncompressedFormattedMatch src dst proto extra) = UncompressedFormattedMatch src ((Neg ip)#dst) proto extra" |
  "iptrule_match_collect (MatchNot (Match (Prot p))) (UncompressedFormattedMatch src dst proto extra) = UncompressedFormattedMatch src dst ((Neg p)#proto) extra"  |
  "iptrule_match_collect (MatchNot (Match (Extra e))) (UncompressedFormattedMatch src dst proto extra) = UncompressedFormattedMatch src dst proto ((Neg e)#extra)" |
  "iptrule_match_collect (MatchAnd m1 m2) fmt =  
     iptrule_match_Ln_uncompressed_append (iptrule_match_collect m1 fmt) 
      (iptrule_match_Ln_uncompressed_append (iptrule_match_collect m2 fmt) fmt)" 



lemma "wf_disc_sel (is_Src, src_range) Src"
  by(simp add: wf_disc_sel.simps)


lemma "normalized_match m \<Longrightarrow> iptrule_match_collect m (UncompressedFormattedMatch [] [] [] []) = (
    let (srcs, m') = primitive_extractor (is_Src, src_range) m;
        (dsts, m'') = primitive_extractor (is_Dst, dst_range) m';
        (protos, m''') = primitive_extractor (is_Prot, prot_sel) m'';
        (extras, m''') = primitive_extractor (is_Extra, extra_sel) m'''
        in UncompressedFormattedMatch srcs dsts protos extras
  )"
apply(induction m "UncompressedFormattedMatch [] [] [] []" rule: iptrule_match_collect.induct)
apply(simp_all)
apply(simp add: split: split_split_asm split_split)
done



(*we dont't have an empty ip space, but a space which only contains the 0 address. We will use the option type to denote the empty space in some functions.*)
lemma "ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal (0, 0, 0, 0)) 33 = {0}"
apply(simp add: ipv4addr_of_dotteddecimal.simps ipv4addr_of_nat_def)
apply(simp add: ipv4range_set_from_bitmask_def)
apply(simp add: ipv4range_set_from_netmask_def)
done

value(code) "iptrule_match_collect (MatchAnd (Match (Src (Ip4AddrNetmask (0, 0, 0, 0) 8))) (Match (Prot ipt_protocol.ProtTCP))) (UncompressedFormattedMatch [] [] [] [])"

thm iptrule_match_collect.induct

lemma srclist_and_append: "matches (\<beta>, \<alpha>) (srclist_and (l1 @ l2)) a p \<longleftrightarrow> matches (\<beta>, \<alpha>)  (MatchAnd (srclist_and l1)  (srclist_and l2)) a p"
  apply(induction l1)
   apply(simp_all add: bunch_of_lemmata_about_matches)
  apply(rename_tac l l1)
  apply(case_tac l)
   apply(simp_all add: bunch_of_lemmata_about_matches)
  done
lemma dstlist_and_append: "matches (\<beta>, \<alpha>) (dstlist_and (l1 @ l2)) a p \<longleftrightarrow> matches (\<beta>, \<alpha>)  (MatchAnd (dstlist_and l1)  (dstlist_and l2)) a p"
  apply(induction l1)
   apply(simp_all add: bunch_of_lemmata_about_matches)
  apply(rename_tac l l1)
  apply(case_tac l)
   apply(simp_all add: bunch_of_lemmata_about_matches)
  done
lemma protolist_and_append: "matches (\<beta>, \<alpha>) (protolist_and (l1 @ l2)) a p \<longleftrightarrow> matches (\<beta>, \<alpha>)  (MatchAnd (protolist_and l1)  (protolist_and l2)) a p"
  apply(induction l1)
   apply(simp_all add: bunch_of_lemmata_about_matches)
  apply(rename_tac l l1)
  apply(case_tac l)
   apply(simp_all add: bunch_of_lemmata_about_matches)
  done
lemma extralist_and_append: "matches (\<beta>, \<alpha>) (extralist_and (l1 @ l2)) a p \<longleftrightarrow> matches (\<beta>, \<alpha>)  (MatchAnd (extralist_and l1)  (extralist_and l2)) a p"
  apply(induction l1)
   apply(simp_all add: bunch_of_lemmata_about_matches)
  apply(rename_tac l l1)
  apply(case_tac l)
   apply(simp_all add: bunch_of_lemmata_about_matches)
  done

lemma matches_iptrule_match_Ln_uncompressed_append: "matches (\<beta>, \<alpha>) (UncompressedFormattedMatch_to_match_expr (iptrule_match_Ln_uncompressed_append fmt1 fmt2)) a p \<longleftrightarrow>
       matches (\<beta>, \<alpha>) (MatchAnd (UncompressedFormattedMatch_to_match_expr fmt1) (UncompressedFormattedMatch_to_match_expr fmt2)) a p"
apply(case_tac fmt1)
apply(case_tac fmt2)
apply(clarify)
apply(simp)
apply(simp add: srclist_and_append dstlist_and_append protolist_and_append extralist_and_append bunch_of_lemmata_about_matches)
by fastforce

text{*The empty matches always match*}
lemma "matches (\<beta>, \<alpha>) (UncompressedFormattedMatch_to_match_expr (UncompressedFormattedMatch [] [] [] [])) a p"
  by(simp add: bunch_of_lemmata_about_matches)

lemma UncompressedFormattedMatch_to_match_expr_correct: assumes "normalized_match m" shows
  "matches (\<beta>, \<alpha>) (UncompressedFormattedMatch_to_match_expr accu) a p \<Longrightarrow> 
      matches (\<beta>, \<alpha>) (UncompressedFormattedMatch_to_match_expr (iptrule_match_collect m accu)) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
using assms apply (induction m accu arbitrary: rule: iptrule_match_collect.induct)
  apply (simp add: eval_ternary_simps ip_in_ipv4range_set_from_bitmask_UNIV bunch_of_lemmata_about_matches)
  apply (simp add: eval_ternary_simps ip_in_ipv4range_set_from_bitmask_UNIV bunch_of_lemmata_about_matches)
  apply (simp add: eval_ternary_simps ip_in_ipv4range_set_from_bitmask_UNIV bunch_of_lemmata_about_matches)
  apply (simp add: eval_ternary_simps ip_in_ipv4range_set_from_bitmask_UNIV bunch_of_lemmata_about_matches)
  apply (simp add: eval_ternary_simps ip_in_ipv4range_set_from_bitmask_UNIV bunch_of_lemmata_about_matches)
  apply (simp add: eval_ternary_simps ip_in_ipv4range_set_from_bitmask_UNIV bunch_of_lemmata_about_matches)
  apply (simp add: eval_ternary_simps ip_in_ipv4range_set_from_bitmask_UNIV bunch_of_lemmata_about_matches)
  apply (simp add: eval_ternary_simps ip_in_ipv4range_set_from_bitmask_UNIV bunch_of_lemmata_about_matches)
  apply (simp add: eval_ternary_simps ip_in_ipv4range_set_from_bitmask_UNIV bunch_of_lemmata_about_matches)
  apply (simp add: eval_ternary_simps ip_in_ipv4range_set_from_bitmask_UNIV bunch_of_lemmata_about_matches)
  apply(simp add: matches_iptrule_match_Ln_uncompressed_append bunch_of_lemmata_about_matches)
  (*the rest are the undefined cases*)
  apply(simp_all) --{*@{text "\<not> normalized_match"}*}
done


definition format_Ln_match :: "iptrule_match match_expr \<Rightarrow> iptrule_match_Ln_uncompressed" where
  "format_Ln_match m \<equiv> iptrule_match_collect m (UncompressedFormattedMatch [] [] [] [])"

corollary format_Ln_match_correct: "normalized_match m \<Longrightarrow> matches (\<beta>, \<alpha>) (UncompressedFormattedMatch_to_match_expr (format_Ln_match m)) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
unfolding format_Ln_match_def
apply(rule UncompressedFormattedMatch_to_match_expr_correct)
apply(simp_all)
apply(simp add: bunch_of_lemmata_about_matches)
done

lemma format_Ln_match_correct': "\<forall> m' \<in> set ms. normalized_match m' \<Longrightarrow> 
    approximating_bigstep_fun (\<beta>, \<alpha>) p (map (\<lambda>m. Rule m a) (map (\<lambda>m'. UncompressedFormattedMatch_to_match_expr (format_Ln_match m')) ms)) s =
    approximating_bigstep_fun (\<beta>, \<alpha>) p (map (\<lambda>m. Rule m a) ms) s"
apply(rule match_list_semantics)
apply(induction ms)
 apply(simp)
apply(simp)
by (metis format_Ln_match_correct)





lemma helper: "\<forall> m' \<in> set ms. normalized_match m' \<Longrightarrow> 
      approximating_bigstep_fun (\<beta>, \<alpha>) p (map ((\<lambda>r. Rule (UncompressedFormattedMatch_to_match_expr (fst r)) (snd r)) \<circ> (\<lambda>r. (format_Ln_match (get_match r), get_action r)) \<circ> (\<lambda>m. Rule m a)) ms) Undecided =
      approximating_bigstep_fun (\<beta>, \<alpha>) p (map (\<lambda> m. Rule m a) ms) Undecided"
apply(induction ms)
 apply(simp add: normalize_match_empty)
apply(simp split: split_if_asm split_if)
apply(safe)
apply(simp_all add: format_Ln_match_correct)
apply(simp split: action.split)
by blast
corollary helper': "(approximating_bigstep_fun (\<beta>, \<alpha>) p (map ((\<lambda>r. Rule (UncompressedFormattedMatch_to_match_expr (fst r)) (snd r)) \<circ> (\<lambda>r. (format_Ln_match (get_match r), get_action r)) \<circ> (\<lambda>m. Rule m a)) (normalize_match m)) Undecided) =
    (approximating_bigstep_fun (\<beta>, \<alpha>) p [Rule m a] Undecided)"
apply(subst helper)
apply (metis normalized_match_normalize_match)
by (metis normalize_match_correct)
hide_fact helper


lemma approximating_bigstep_fun_seq_wf_fst: "wf_ruleset \<gamma> p [Rule m a] \<Longrightarrow> approximating_bigstep_fun \<gamma> p (Rule m a # rs\<^sub>2) Undecided = approximating_bigstep_fun \<gamma> p rs\<^sub>2 (approximating_bigstep_fun \<gamma> p [Rule m a] Undecided)"
using approximating_bigstep_fun_seq_wf[where rs\<^sub>1="[Rule m a]"] by (metis append_Cons append_Nil)

definition format_Ln_rules_uncompressed :: "iptrule_match rule list \<Rightarrow> (iptrule_match_Ln_uncompressed \<times> action) list" where
  "format_Ln_rules_uncompressed rs = [((format_Ln_match (get_match r)), (get_action r)). r \<leftarrow> (normalize_rules rs)]"

definition Ln_rules_to_rule :: "(iptrule_match_Ln_uncompressed \<times> action) list \<Rightarrow> iptrule_match rule list" where
  "Ln_rules_to_rule rs = [Rule (UncompressedFormattedMatch_to_match_expr (fst r)) (snd r). r \<leftarrow> rs]"


lemma Ln_rules_to_rule_head: "Ln_rules_to_rule (r#rs) = (Rule (UncompressedFormattedMatch_to_match_expr (fst r)) (snd r))#Ln_rules_to_rule rs"
  by(simp add: Ln_rules_to_rule_def)



lemma Ln_rules_to_rule_format_Ln_rules: "Ln_rules_to_rule (format_Ln_rules_uncompressed rs) = [Rule (UncompressedFormattedMatch_to_match_expr (format_Ln_match (get_match r))) (get_action r). r \<leftarrow> (normalize_rules rs)]"
  apply(induction rs)
   apply(simp_all add: Ln_rules_to_rule_def format_Ln_rules_uncompressed_def)
  done

lemma format_Ln_rules_uncompressed_correct: "good_ruleset rs \<Longrightarrow> 
    approximating_bigstep_fun (\<beta>, \<alpha>) p (Ln_rules_to_rule (format_Ln_rules_uncompressed rs)) s = 
    approximating_bigstep_fun (\<beta>, \<alpha>) p rs s"
  apply(case_tac s)
   prefer 2
   apply(simp add: Decision_approximating_bigstep_fun)
  apply(clarify)
  unfolding Ln_rules_to_rule_def format_Ln_rules_uncompressed_def
  apply(induction rs)
   apply(simp)
  apply(simp)
  apply(subst normalize_rules_fst)
  apply(rename_tac r rs)
  apply(case_tac r, rename_tac m a)
  apply(clarify)
  apply(simp del: approximating_bigstep_fun.simps)
  apply(frule good_ruleset_fst)
  apply(drule good_ruleset_tail)
  apply(simp del: approximating_bigstep_fun.simps)
  apply(frule good_ruleset_normalize_match)
  apply(subst approximating_bigstep_fun_seq_wf)
  defer
  apply(subst helper')
  
  apply(subst(2) approximating_bigstep_fun_seq_wf_fst)
   apply(simp add: good_imp_wf_ruleset)
  apply(case_tac "(approximating_bigstep_fun (\<beta>, \<alpha>) p [Rule m a] Undecided)")
   apply(simp)
  apply (metis Decision_approximating_bigstep_fun)

  apply(thin_tac "approximating_bigstep_fun ?\<gamma> p ?rs1 Undecided = approximating_bigstep_fun ?\<gamma> p ?rs2 Undecided")
  apply(simp add: wf_ruleset_def)
  apply(clarify)
  apply(simp add: good_ruleset_alt)
  apply blast
  done





text{*Isolating the matching semantics*}
fun nt_match_list :: "('a, 'packet) match_tac \<Rightarrow> action \<Rightarrow> 'packet \<Rightarrow> 'a negation_type list \<Rightarrow> bool" where
  "nt_match_list _ _ _ [] = True" |
  "nt_match_list \<gamma> a p ((Pos x)#xs) \<longleftrightarrow> matches \<gamma> (Match x) a p \<and> nt_match_list \<gamma> a p xs" |
  "nt_match_list \<gamma> a p ((Neg x)#xs) \<longleftrightarrow> matches \<gamma> (MatchNot (Match x)) a p \<and> nt_match_list \<gamma> a p xs"

lemma nt_match_list_matches: "nt_match_list \<gamma> a p l \<longleftrightarrow> matches \<gamma> (alist_and l) a p"
  apply(induction l rule: alist_and.induct)
  apply(simp_all)
  apply(case_tac [!] \<gamma>)
  apply(simp_all add: bunch_of_lemmata_about_matches)
done


lemma nt_match_list_simp: "nt_match_list \<gamma> a p ms \<longleftrightarrow> 
      (\<forall>m \<in> set (getPos ms). matches \<gamma> (Match m) a p) \<and> (\<forall>m \<in> set (getNeg ms). matches \<gamma> (MatchNot (Match m)) a p)"
apply(induction \<gamma> a p ms rule: nt_match_list.induct)
apply(simp_all)
by fastforce

lemma matches_alist_and: "matches \<gamma> (alist_and l) a p \<longleftrightarrow> (\<forall>m \<in> set (getPos l). matches \<gamma> (Match m) a p) \<and> (\<forall>m \<in> set (getNeg l). matches \<gamma> (MatchNot (Match m)) a p)"
by (metis (poly_guards_query) nt_match_list_matches nt_match_list_simp)



fun Ln_uncompressed_matching :: "(iptrule_match, 'packet) match_tac \<Rightarrow> action \<Rightarrow> 'packet \<Rightarrow> iptrule_match_Ln_uncompressed \<Rightarrow> bool" where
  "Ln_uncompressed_matching \<gamma> a p (UncompressedFormattedMatch src dst proto extra) \<longleftrightarrow> 
    (nt_match_list \<gamma> a p (NegPos_map Src src)) \<and>
    (nt_match_list \<gamma> a p (NegPos_map Dst dst)) \<and>
    (nt_match_list \<gamma> a p (NegPos_map Prot proto)) \<and>
    (nt_match_list \<gamma> a p (NegPos_map Extra extra))"

declare Ln_uncompressed_matching.simps[simp del]

lemma Ln_uncompressed_matching: "Ln_uncompressed_matching \<gamma> a p m \<longleftrightarrow> matches \<gamma> (UncompressedFormattedMatch_to_match_expr m) a p"
  apply(cases m)
  apply(simp)
  apply(simp add: list_and_simps1 list_and_simps2 list_and_simps3 list_and_simps4)
  apply(simp add: nt_match_list_matches Ln_uncompressed_matching.simps)
by (metis matches_simp1 matches_simp2)



lemma Ln_uncompressed_matching_semantics_singleton: "Ln_uncompressed_matching \<gamma> a p m1 \<longleftrightarrow> Ln_uncompressed_matching \<gamma> a p m2
  \<Longrightarrow> approximating_bigstep_fun \<gamma> p (Ln_rules_to_rule [(m1, a)]) s = 
      approximating_bigstep_fun \<gamma> p (Ln_rules_to_rule [(m2, a)]) s"
  apply(case_tac s)
   prefer 2
   apply(simp add: Decision_approximating_bigstep_fun)
  apply(clarify)
  apply(simp add: Ln_rules_to_rule_def)
  apply(simp split: action.split)
  apply(simp add: Ln_uncompressed_matching)
  apply(safe)
  done




end

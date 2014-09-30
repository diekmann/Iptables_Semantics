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


(*this is the thing we have at the moment. Todo: compress the lists to one entry*)
datatype iptrule_match_Ln_uncompressed = UncompressedFormattedMatch 
  (*Src*) "ipt_ipv4range negation_type list"
  (*Dst*) "ipt_ipv4range negation_type list"
  (*Prot*) "ipt_protocol negation_type list"
  (*Extra*) "string negation_type list"


text{*Transform a @{typ "'a negation_type list"} to a @{typ "'a match_expr"} via conjunction.*}
fun alist_and :: "'a negation_type list \<Rightarrow> 'a match_expr" where
  "alist_and [] = MatchAny" |
  "alist_and ((Pos e)#es) = MatchAnd (Match e) (alist_and es)" |
  "alist_and ((Neg e)#es) = MatchAnd (MatchNot (Match e)) (alist_and es)"


fun UncompressedFormattedMatch_to_match_expr :: "iptrule_match_Ln_uncompressed \<Rightarrow> iptrule_match match_expr" where
  "UncompressedFormattedMatch_to_match_expr (UncompressedFormattedMatch src dst proto extra) = 
    MatchAnd (alist_and (NegPos_map Src src)) (MatchAnd (alist_and (NegPos_map Dst dst)) (MatchAnd (alist_and (NegPos_map Prot proto)) (alist_and (NegPos_map Extra extra))))"


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


text{*
We can express @{const iptrule_match_collect} with @{const primitive_extractor}.
Latter is more elegant.
We keep the definition of @{const iptrule_match_collect} to show explicitly what we are doing here.
*}
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


value(code) "iptrule_match_collect (MatchAnd (Match (Src (Ip4AddrNetmask (0, 0, 0, 0) 8))) (Match (Prot ipt_protocol.ProtTCP))) (UncompressedFormattedMatch [] [] [] [])"


lemma alist_and_append: "matches (\<beta>, \<alpha>) (alist_and (l1 @ l2)) a p \<longleftrightarrow> matches (\<beta>, \<alpha>)  (MatchAnd (alist_and l1)  (alist_and l2)) a p"
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
apply(simp add: alist_and_append NegPos_map_append bunch_of_lemmata_about_matches)
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

theory Format_Ln
imports Negation_Type_Matching "../Bitmagic/Numberwang_Ln" "../Primitive_Matchers/IPSpace_Syntax" "../Bitmagic/IPv4Addr"
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


(*this is the thing we have at the moment. Todo: compress the first four lists to one entry*)
datatype match_Ln_uncompressed = UncompressedFormattedMatch 
  (*Src*) "ipt_ipv4range negation_type list"
  (*Dst*) "ipt_ipv4range negation_type list"
  (*Prot*) "ipt_protocol negation_type list"
  (*Extra*) "string negation_type list"


fun UncompressedFormattedMatch_to_match_expr :: "match_Ln_uncompressed \<Rightarrow> iptrule_match match_expr" where
  "UncompressedFormattedMatch_to_match_expr (UncompressedFormattedMatch src dst proto extra) = 
    MatchAnd (alist_and (NegPos_map Src src)) (MatchAnd (alist_and (NegPos_map Dst dst)) (MatchAnd (alist_and (NegPos_map Prot proto)) (alist_and (NegPos_map Extra extra))))"


text{*append*}
  fun match_Ln_uncompressed_append :: "match_Ln_uncompressed \<Rightarrow> match_Ln_uncompressed \<Rightarrow> match_Ln_uncompressed" where
    "match_Ln_uncompressed_append (UncompressedFormattedMatch src1 dst1 proto1 extra1) (UncompressedFormattedMatch src2 dst2 proto2 extra2) = 
          UncompressedFormattedMatch (src1@src2) (dst1@dst2) (proto1@proto2) (extra1@extra2)"
  
  lemma matches_match_Ln_uncompressed_append: "matches \<gamma> (UncompressedFormattedMatch_to_match_expr (match_Ln_uncompressed_append fmt1 fmt2)) a p \<longleftrightarrow>
         matches \<gamma> (MatchAnd (UncompressedFormattedMatch_to_match_expr fmt1) (UncompressedFormattedMatch_to_match_expr fmt2)) a p"
  apply(case_tac fmt1)
  apply(case_tac fmt2)
  apply(clarify)
  apply(simp)
  apply(simp add: alist_and_append NegPos_map_append bunch_of_lemmata_about_matches)
  by fastforce

text{* assumes: @{const "normalized_match"}*}
fun iptrule_match_collect :: "iptrule_match match_expr \<Rightarrow> match_Ln_uncompressed \<Rightarrow> match_Ln_uncompressed" where
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
     match_Ln_uncompressed_append (iptrule_match_collect m1 fmt) 
      (match_Ln_uncompressed_append (iptrule_match_collect m2 fmt) fmt)" 


text{*
We can express @{const iptrule_match_collect} with @{const primitive_extractor}.
Latter is more elegant.
We keep the definition of @{const iptrule_match_collect} to show explicitly what we are doing here.
*}
lemma iptrule_match_collect_by_primitive_extractor: "normalized_match m \<Longrightarrow> iptrule_match_collect m (UncompressedFormattedMatch [] [] [] []) = (
    let (srcs, m') = primitive_extractor (is_Src, src_range) m;
        (dsts, m'') = primitive_extractor (is_Dst, dst_range) m';
        (protos, m''') = primitive_extractor (is_Prot, prot_sel) m'';
        (extras, _) = primitive_extractor (is_Extra, extra_sel) m'''
        in UncompressedFormattedMatch srcs dsts protos extras
  )"
apply(induction m "UncompressedFormattedMatch [] [] [] []" rule: iptrule_match_collect.induct)
apply(simp_all)
apply(simp add: split: split_split_asm split_split)
done


text{*Example*}
lemma "iptrule_match_collect (MatchAnd (Match (Src (Ip4AddrNetmask (0, 0, 0, 0) 8))) (Match (Prot ProtTCP))) (UncompressedFormattedMatch [] [] [] []) =
  UncompressedFormattedMatch [Pos (Ip4AddrNetmask (0, 0, 0, 0) 8)] [] [Pos ProtTCP] []" by eval



text{*The empty @{const UncompressedFormattedMatch} always match*}
lemma "matches \<gamma> (UncompressedFormattedMatch_to_match_expr (UncompressedFormattedMatch [] [] [] [])) a p"
  by(simp add: bunch_of_lemmata_about_matches)

lemma UncompressedFormattedMatch_to_match_expr_correct: assumes "normalized_match m" and "matches \<gamma> (UncompressedFormattedMatch_to_match_expr accu) a p" shows
  "matches \<gamma> (UncompressedFormattedMatch_to_match_expr (iptrule_match_collect m accu)) a p \<longleftrightarrow> matches \<gamma> m a p"
using assms apply (induction m accu arbitrary: rule: iptrule_match_collect.induct)
  apply(case_tac [!] \<gamma>)
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
  apply(simp add: matches_match_Ln_uncompressed_append bunch_of_lemmata_about_matches)
  (*the rest are the undefined cases*)
  apply(simp_all) --{*@{text "\<not> normalized_match"}*}
done



definition format_Ln_match :: "iptrule_match match_expr \<Rightarrow> match_Ln_uncompressed" where
  "format_Ln_match m \<equiv> iptrule_match_collect m (UncompressedFormattedMatch [] [] [] [])"

corollary format_Ln_match_correct: "normalized_match m \<Longrightarrow> matches \<gamma> (UncompressedFormattedMatch_to_match_expr (format_Ln_match m)) a p \<longleftrightarrow> matches \<gamma> m a p"
unfolding format_Ln_match_def
apply(rule UncompressedFormattedMatch_to_match_expr_correct)
 apply(assumption)
by(simp add: bunch_of_lemmata_about_matches)


text{*We can also show the previous corollary by the correctness of @{const primitive_extractor}*}
corollary "normalized_match m \<Longrightarrow> matches \<gamma> (UncompressedFormattedMatch_to_match_expr (format_Ln_match m)) a p \<longleftrightarrow> matches \<gamma> m a p"
proof -
  {fix yc
    have "normalized_match yc \<Longrightarrow> \<not> has_disc is_Dst yc \<Longrightarrow> \<not> has_disc is_Prot yc \<Longrightarrow> \<not> has_disc is_Extra yc \<Longrightarrow> \<not> has_disc is_Src yc \<Longrightarrow> matches \<gamma> yc a p"
    apply(induction yc)
    apply(simp_all add:bunch_of_lemmata_about_matches)
    apply(case_tac aa)
    apply(simp_all)
    apply(case_tac yc)
    apply(simp_all)
    apply(case_tac aa)
    apply(simp_all)
    done
  } note yc_exhaust=this
  assume normalized: "normalized_match m" 
  {fix asrc msrc adst mdst aprot mprot aextra mextra
  from normalized have
      "primitive_extractor (is_Extra, extra_sel) mprot = (aextra, mextra) \<Longrightarrow>
       primitive_extractor (is_Prot, prot_sel) mdst = (aprot, mprot) \<Longrightarrow>
       primitive_extractor (is_Dst, dst_range) msrc = (adst, mdst) \<Longrightarrow>
       primitive_extractor (is_Src, src_range) m = (asrc, msrc) \<Longrightarrow>
        matches \<gamma> (alist_and (NegPos_map Src asrc)) a p \<and>
        matches \<gamma> (alist_and (NegPos_map Dst adst)) a p \<and>
        matches \<gamma> (alist_and (NegPos_map Prot aprot)) a p \<and>
        matches \<gamma> (alist_and (NegPos_map Extra aextra)) a p \<longleftrightarrow> matches \<gamma> m a p"
    apply -
    apply(erule(1) primitive_extractor_matchesE[OF wf_disc_sel_iptrule_match(1)])
    apply(erule(1) primitive_extractor_matchesE[OF wf_disc_sel_iptrule_match(2)])
    apply(erule(1) primitive_extractor_matchesE[OF wf_disc_sel_iptrule_match(3)])
    apply(erule(1) primitive_extractor_matches_lastE[OF wf_disc_sel_iptrule_match(4)])
    using yc_exhaust by metis
  }
  thus ?thesis
    unfolding format_Ln_match_def 
    unfolding iptrule_match_collect_by_primitive_extractor[OF normalized]
    by(simp split: split_split add: bunch_of_lemmata_about_matches(1))
qed



lemma format_Ln_match_correct': "\<forall> m' \<in> set ms. normalized_match m' \<Longrightarrow> 
    approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) (map (\<lambda>m'. UncompressedFormattedMatch_to_match_expr (format_Ln_match m')) ms)) s =
    approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) ms) s"
apply(rule match_list_semantics)
apply(induction ms)
 apply(simp)
apply(simp)
by (metis format_Ln_match_correct)



definition format_Ln_rules_uncompressed :: "iptrule_match rule list \<Rightarrow> (match_Ln_uncompressed \<times> action) list" where
  "format_Ln_rules_uncompressed rs = [((format_Ln_match (get_match r)), (get_action r)). r \<leftarrow> (normalize_rules rs)]"

definition Ln_rules_to_rule :: "(match_Ln_uncompressed \<times> action) list \<Rightarrow> iptrule_match rule list" where
  "Ln_rules_to_rule rs = [case r of (m,a) \<Rightarrow> Rule (UncompressedFormattedMatch_to_match_expr m) a. r \<leftarrow> rs]"


lemma format_Ln_rules_uncompressed_correct: "good_ruleset rs \<Longrightarrow> 
    approximating_bigstep_fun \<gamma> p (Ln_rules_to_rule (format_Ln_rules_uncompressed rs)) s = approximating_bigstep_fun \<gamma> p rs s"
proof(induction rs)
case Nil thus ?case by(simp add: Ln_rules_to_rule_def format_Ln_rules_uncompressed_def)
next
case (Cons r rs)
  from Cons.IH Cons.prems good_ruleset_tail have IH: "approximating_bigstep_fun \<gamma> p (Ln_rules_to_rule (format_Ln_rules_uncompressed rs)) s = approximating_bigstep_fun \<gamma> p rs s"
    by blast

  have map_uncompressedmapping_simp: "\<And>ms a. (map ((\<lambda>(m, y). Rule (UncompressedFormattedMatch_to_match_expr m) y) \<circ> (\<lambda>r. (format_Ln_match (get_match r), get_action r)) \<circ> (\<lambda>m. Rule m a)) ms) =
       (map (\<lambda>m. Rule m a) (map (\<lambda>m'. UncompressedFormattedMatch_to_match_expr (format_Ln_match m')) ms))" by(simp)

  let ?rsA="map ((\<lambda>(m, y). Rule (UncompressedFormattedMatch_to_match_expr m) y) \<circ> (\<lambda>r. (format_Ln_match (get_match r), get_action r))) (normalize_rules [r])"
  let ?rsC="map ((\<lambda>(m, y). Rule (UncompressedFormattedMatch_to_match_expr m) y) \<circ> (\<lambda>r. (format_Ln_match (get_match r), get_action r))) (normalize_rules rs)"
  from approximating_bigstep_fun_wf_postpend[where rsB="[r]", simplified] have subst_rule:
    "\<And>rsA rsC. wf_ruleset \<gamma> p rsA \<Longrightarrow> wf_ruleset \<gamma> p [r] \<Longrightarrow>
    approximating_bigstep_fun \<gamma> p rsA s = approximating_bigstep_fun \<gamma> p [r] s \<Longrightarrow> approximating_bigstep_fun \<gamma> p (rsA @ rsC) s = approximating_bigstep_fun \<gamma> p (r # rsC) s"
    by fast
  
  have "approximating_bigstep_fun \<gamma> p (Ln_rules_to_rule (format_Ln_rules_uncompressed (r # rs))) s = 
        approximating_bigstep_fun \<gamma> p
             (map ((\<lambda>(m, y). Rule (UncompressedFormattedMatch_to_match_expr m) y) \<circ> (\<lambda>r. (format_Ln_match (get_match r), get_action r))) (normalize_rules (r # rs))) s"
    by (simp add: Ln_rules_to_rule_def format_Ln_rules_uncompressed_def)
  also have "... = approximating_bigstep_fun \<gamma> p (?rsA @ ?rsC) s" by(subst normalize_rules_fst, simp)
  also have "... = approximating_bigstep_fun \<gamma> p (r # ?rsC) s" 
    proof(subst subst_rule)
      from Cons.prems good_ruleset_fst have "good_ruleset [r]" by fast
      hence "good_ruleset ?rsA"
       apply(cases r)
       apply(rename_tac m a,clarify)
       apply(simp add: normalize_rules_singleton)
       apply(drule good_ruleset_normalize_match)
       apply(simp add: good_ruleset_alt)
       done
      thus "wf_ruleset \<gamma> p ?rsA" using good_imp_wf_ruleset by fast
    next
      show "wf_ruleset \<gamma> p [r]" using Cons.prems good_ruleset_fst good_imp_wf_ruleset by fast
    next
      show "approximating_bigstep_fun \<gamma> p ?rsA s = approximating_bigstep_fun \<gamma> p [r] s"
       apply(case_tac r, rename_tac m a, clarify)
       apply(simp add: normalize_rules_singleton)
       apply(simp add: map_uncompressedmapping_simp)
       apply(subst normalize_match_correct[symmetric])
       apply(subst format_Ln_match_correct'[symmetric])
        apply(simp add: normalized_match_normalize_match)
       apply(simp)
       done
     next
      show "approximating_bigstep_fun \<gamma> p (r#?rsC) s = approximating_bigstep_fun \<gamma> p (r#?rsC) s" by blast
     qed
  also have " ... = approximating_bigstep_fun \<gamma> p (r # Ln_rules_to_rule (format_Ln_rules_uncompressed rs)) s"
    by (simp add: Ln_rules_to_rule_def format_Ln_rules_uncompressed_def)
  also have "... = approximating_bigstep_fun \<gamma> p (r # rs) s " using IH approximating_bigstep_fun_singleton_prepend by fast
  finally show ?case .
qed


(*
lemma approximating_bigstep_fun_seq_wf_fst: "wf_ruleset \<gamma> p [Rule m a] \<Longrightarrow> approximating_bigstep_fun \<gamma> p (Rule m a # rs\<^sub>2) Undecided = approximating_bigstep_fun \<gamma> p rs\<^sub>2 (approximating_bigstep_fun \<gamma> p [Rule m a] Undecided)"
using approximating_bigstep_fun_seq_wf[where rs\<^sub>1="[Rule m a]"] by (metis append_Cons append_Nil)
*)


(*Move up, simplify stuff?*)
fun Ln_uncompressed_matching :: "(iptrule_match, 'packet) match_tac \<Rightarrow> action \<Rightarrow> 'packet \<Rightarrow> match_Ln_uncompressed \<Rightarrow> bool" where
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

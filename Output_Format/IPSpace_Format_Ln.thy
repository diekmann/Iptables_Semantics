theory IPSpace_Format_Ln
imports Format_Ln "../Primitive_Matchers/IPSpace_Matcher" IPSpace_Operations
begin


subsection{*Formatting*}

lemma "(\<Inter>x\<in>set X. ipv4s_to_set x) = {} \<Longrightarrow> \<not> (\<forall>m\<in>set X. matches (simple_matcher, \<alpha>) (Match (Src m)) a p)"
  using simple_matcher_SrcDst_Inter by blast
  

lemma compress_pos_ips_src_None_matching: "compress_pos_ips src' = None \<Longrightarrow> 
  \<not> Ln_uncompressed_matching (simple_matcher, \<alpha>) a p (UncompressedFormattedMatch (map Pos src') dst proto extra)"
  apply(simp add: compress_pos_ips_None)
  apply(unfold Ln_uncompressed_matching.simps)
  apply safe
  apply(thin_tac "nt_match_list (simple_matcher, \<alpha>) a p (NegPos_map Dst dst)")
  apply(thin_tac "nt_match_list (simple_matcher, \<alpha>) a p (NegPos_map Prot proto)")
  apply(thin_tac "nt_match_list (simple_matcher, \<alpha>) a p (NegPos_map Extra extra)")
  apply(simp add: nt_match_list_simp)
  apply(simp add: getPos_NegPos_map_simp)
  using simple_matcher_SrcDst_Inter by blast
lemma compress_pos_ips_dst_None_matching: "compress_pos_ips dst = None \<Longrightarrow> 
  \<not> Ln_uncompressed_matching (simple_matcher, \<alpha>) a p (UncompressedFormattedMatch src (map Pos dst) proto extra)"
  apply(simp add: compress_pos_ips_None)
  apply(unfold Ln_uncompressed_matching.simps)
  apply safe
  apply(thin_tac " nt_match_list (simple_matcher, \<alpha>) a p (NegPos_map Src ?x)")
  apply(thin_tac " nt_match_list (simple_matcher, \<alpha>) a p (NegPos_map Prot proto)")
  apply(thin_tac " nt_match_list (simple_matcher, \<alpha>) a p (NegPos_map Extra extra)")
  apply(simp add: nt_match_list_simp)
  apply(simp add: getPos_NegPos_map_simp)
  using simple_matcher_SrcDst_Inter by blast


lemma compress_pos_ips_src_Some_matching: "compress_pos_ips src' = Some X \<Longrightarrow> 
  matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Src [Pos X])) a p \<longleftrightarrow>
  matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Src (map Pos src')))a p"
  apply(drule compress_pos_ips_Some)
  apply(simp only: nt_match_list_matches[symmetric])
  apply safe
   apply(simp add: nt_match_list_simp)
   apply(simp add: getPos_NegPos_map_simp)
   apply(rule conjI)
    apply(simp add: simple_matcher_SrcDst_Inter)
    apply(simp add: match_simplematcher_SrcDst)
   apply(simp add: getNeg_Pos_empty)
  apply(simp add: match_simplematcher_SrcDst)
  apply(simp add: nt_match_list_simp)
  apply(simp add: getPos_NegPos_map_simp)
  apply(simp add: simple_matcher_SrcDst_Inter)
  done
lemma compress_pos_ips_dst_Some_matching: "compress_pos_ips dst' = Some X \<Longrightarrow> 
  matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Dst [Pos X])) a p \<longleftrightarrow>
  matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Dst (map Pos dst')))a p"
  apply(drule compress_pos_ips_Some)
  apply(simp only: nt_match_list_matches[symmetric]) (*better use matches_alist_and*)
  apply safe
   apply(simp add: nt_match_list_simp)
   apply(simp add: getPos_NegPos_map_simp)
   apply(rule conjI)
    apply(simp add: simple_matcher_SrcDst_Inter)
    apply(simp add: match_simplematcher_SrcDst)
   apply(simp add: getNeg_Pos_empty)
  apply(simp add: match_simplematcher_SrcDst)
  apply(simp add: nt_match_list_simp)
  apply(simp add: getPos_NegPos_map_simp)
  apply(simp add: simple_matcher_SrcDst_Inter)
  done
(*careful, compress_pos_ips_dst_Some_matching and compress_pos_ips_src_Some_matching are very similar*)




lemma Ln_uncompressed_matching_src_dst_subset: "set (src') \<subseteq> set (src) \<Longrightarrow> 
    Ln_uncompressed_matching (simple_matcher, \<alpha>) a p (UncompressedFormattedMatch src dst proto extra) \<Longrightarrow>
    Ln_uncompressed_matching (simple_matcher, \<alpha>) a p (UncompressedFormattedMatch src' dst proto extra)"
  "set (dst') \<subseteq> set (dst) \<Longrightarrow> 
    Ln_uncompressed_matching (simple_matcher, \<alpha>) a p (UncompressedFormattedMatch src dst proto extra) \<Longrightarrow>
    Ln_uncompressed_matching (simple_matcher, \<alpha>) a p (UncompressedFormattedMatch src dst' proto extra)"
  apply(simp_all only: Ln_uncompressed_matching.simps nt_match_list_matches)
  apply(safe)
  apply(thin_tac "matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Dst ?x)) a p")
  apply(thin_tac "matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Prot ?x)) a p")
  apply(thin_tac "matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Extra ?x)) a p")
  prefer 2
  apply(thin_tac "matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Src ?x)) a p")
  apply(thin_tac "matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Prot ?x)) a p")
  apply(thin_tac "matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Extra ?x)) a p")
  prefer 2
  apply(simp_all add: matches_alist_and)
  apply(simp_all add: NegPos_map_simps)
  apply(simp_all add: match_simplematcher_SrcDst match_simplematcher_SrcDst_not)
  apply(clarify)
  apply(simp_all add: NegPos_set)
  apply blast
  apply(clarify)
  apply(blast) 
done


lemma compress_ips_src_None_matching: "compress_ips src = None \<Longrightarrow> \<not> Ln_uncompressed_matching (simple_matcher, \<alpha>) a p (UncompressedFormattedMatch src dst proto extra)"
  apply(case_tac "getPos src = []")
   apply(simp)
  apply(simp split: option.split_asm)
   apply(drule_tac \<alpha>=\<alpha> and a=a and p=p and dst=dst and proto=proto and extra=extra in compress_pos_ips_src_None_matching)
   apply(thin_tac "getPos src \<noteq> []")
   apply(erule HOL.rev_notE)
   apply(simp)
   apply(rule_tac src'="(map Pos (getPos src))" and src=src in Ln_uncompressed_matching_src_dst_subset(1))
    prefer 2 apply simp
   apply(simp)
   apply(simp add: NegPos_set)
  apply(simp split: split_if_asm)
  apply(drule compress_pos_ips_Some)
  apply(simp add: ipv4range_to_set_collect_to_range ipv4range_set_from_bitmask_to_executable_ipv4range)
  apply(simp add: Ln_uncompressed_matching.simps nt_match_list_matches)
  apply(clarify)
  apply(thin_tac "matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Dst ?x)) a p")
  apply(thin_tac "matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Prot ?x)) a p")
  apply(thin_tac "matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Extra ?x)) a p")
  apply(simp add: matches_alist_and)
  apply(simp add: NegPos_map_simps)
  apply(simp add: match_simplematcher_SrcDst match_simplematcher_SrcDst_not)
  apply(clarify)
by (metis (erased, hide_lams) INT_iff UN_iff subsetCE)
lemma compress_ips_dst_None_matching: "compress_ips dst = None \<Longrightarrow> \<not> Ln_uncompressed_matching (simple_matcher, \<alpha>) a p (UncompressedFormattedMatch src dst proto extra)"
  apply(case_tac "getPos dst = []")
   apply(simp)
  apply(simp split: option.split_asm)
   apply(drule_tac \<alpha>=\<alpha> and a=a and p=p and src=src and proto=proto and extra=extra in compress_pos_ips_dst_None_matching)
   apply(thin_tac "getPos dst \<noteq> []")
   apply(erule HOL.rev_notE)
   apply(simp)
   apply(rule_tac dst'="(map Pos (getPos dst))" and dst=dst in Ln_uncompressed_matching_src_dst_subset(2))
    prefer 2 apply simp
   apply(simp)
   apply(simp add: NegPos_set)
  apply(simp split: split_if_asm)
  apply(drule compress_pos_ips_Some)
  apply(simp add: ipv4range_to_set_collect_to_range ipv4range_set_from_bitmask_to_executable_ipv4range)
  apply(simp add: Ln_uncompressed_matching.simps nt_match_list_matches)
  apply(clarify)
  apply(thin_tac "matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Src ?x)) a p")
  apply(thin_tac "matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Prot ?x)) a p")
  apply(thin_tac "matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Extra ?x)) a p")
  apply(simp add: matches_alist_and)
  apply(simp add: NegPos_map_simps)
  apply(simp add: match_simplematcher_SrcDst match_simplematcher_SrcDst_not)
  apply(clarify)
by (metis (erased, hide_lams) INT_iff UN_iff subsetCE)

lemma Ln_uncompressed_matching_src_eq: "matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Src X)) a p \<longleftrightarrow> matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Src Y)) a p \<Longrightarrow>
       Ln_uncompressed_matching (simple_matcher, \<alpha>) a p (UncompressedFormattedMatch X dst proto extra) \<longleftrightarrow>
       Ln_uncompressed_matching (simple_matcher, \<alpha>) a p (UncompressedFormattedMatch Y dst proto extra)"
apply(simp add: Ln_uncompressed_matching)
by (metis matches_simp11 matches_simp22)


(*X \<and> A \<longleftrightarrow> Y \<and> B would be more generic*)
lemma Ln_uncompressed_matching_src_dst_eq: "matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Src X)) a p \<longleftrightarrow> matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Src Y)) a p \<Longrightarrow>
       matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Dst A)) a p \<longleftrightarrow> matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Dst B)) a p \<Longrightarrow>
       Ln_uncompressed_matching (simple_matcher, \<alpha>) a p (UncompressedFormattedMatch X A proto extra) \<longleftrightarrow>
       Ln_uncompressed_matching (simple_matcher, \<alpha>) a p (UncompressedFormattedMatch Y B proto extra)"
apply(simp add: Ln_uncompressed_matching)
by (metis matches_simp11 matches_simp22)

(*todo: move*)
lemma matches_and_x_any: "matches \<gamma> (MatchAnd (Match x) MatchAny) a p = matches \<gamma> (Match x) a p "
  apply(case_tac \<gamma>)
  by(simp add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)

lemma compress_ips_src_Some_matching: "compress_ips src = Some X \<Longrightarrow> 
    matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Src X)) a p \<longleftrightarrow> matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Src src)) a p"
  apply(case_tac "getPos src = []")
   apply(simp)
  apply(simp)
  apply(simp split: option.split_asm split_if_asm)
  apply(simp add: ipv4range_set_from_bitmask_to_executable_ipv4range ipv4range_to_set_collect_to_range)
  apply(drule_tac \<alpha>=\<alpha> and a=a and p=p in compress_pos_ips_src_Some_matching)
  apply(simp add: matches_and_x_any)
  apply(simp add: matches_alist_and NegPos_map_simps match_simplematcher_SrcDst match_simplematcher_SrcDst_not)
  apply(safe)
  apply(simp_all add: NegPos_map_simps)
  done
lemma compress_ips_dst_Some_matching: "compress_ips dst = Some X \<Longrightarrow> 
    matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Dst X)) a p \<longleftrightarrow> matches (simple_matcher, \<alpha>) (alist_and (NegPos_map Dst dst)) a p"
  apply(case_tac "getPos dst = []")
   apply(simp)
  apply(simp)
  apply(simp split: option.split_asm split_if_asm)
  apply(simp add: ipv4range_set_from_bitmask_to_executable_ipv4range ipv4range_to_set_collect_to_range)
  apply(drule_tac \<alpha>=\<alpha> and a=a and p=p in compress_pos_ips_dst_Some_matching)
  apply(simp add: matches_and_x_any)
  apply(simp add: matches_alist_and NegPos_map_simps match_simplematcher_SrcDst match_simplematcher_SrcDst_not)
  apply(safe)
  apply(simp_all add: NegPos_map_simps)
  done

fun compress_Ln_ips :: "(iptrule_match_Ln_uncompressed \<times> action) list \<Rightarrow> (iptrule_match_Ln_uncompressed \<times> action) list" where
  "compress_Ln_ips [] = []" |
  "compress_Ln_ips (((UncompressedFormattedMatch src dst proto extra), a)#rs) =
    (case (compress_ips src, compress_ips dst) of
      (None, _) \<Rightarrow> compress_Ln_ips rs
    | (_, None) \<Rightarrow> compress_Ln_ips rs
    | (Some src', Some dst') \<Rightarrow> (UncompressedFormattedMatch src' dst' proto extra, a)#(compress_Ln_ips rs)
    )"

export_code compress_Ln_ips in SML



(*TODO correctness proof*)
fun compress_ports :: "ipt_protocol negation_type list \<Rightarrow> ipt_protocol negation_type option" where
  "compress_ports [] = Some (Pos ProtAll)" |
  "compress_ports ((Pos ProtAll)#ps) = compress_ports ps" |
  "compress_ports ((Neg ProtAll)#_) = None" | 
  "compress_ports ( p # Pos ProtAll # ps) = compress_ports (p#ps)"|
  "compress_ports ( _ # Neg ProtAll # _) = None" |
  "compress_ports ( Pos ProtTCP # Pos ProtUDP # _) = None"|
  "compress_ports ( Pos ProtUDP # Pos ProtTCP # _) = None"


lemma approximating_bigstep_fun_Ln_rules_to_rule_step_simultaneously:
  "approximating_bigstep_fun (simple_matcher, \<alpha>) p (Ln_rules_to_rule (rs1)) Undecided = approximating_bigstep_fun (simple_matcher, \<alpha>) p (Ln_rules_to_rule (rs2)) Undecided \<Longrightarrow>
  matches (simple_matcher, \<alpha>) (UncompressedFormattedMatch_to_match_expr r1) a p \<longleftrightarrow> matches (simple_matcher, \<alpha>) (UncompressedFormattedMatch_to_match_expr r2) a p
  \<Longrightarrow>
  approximating_bigstep_fun (simple_matcher, \<alpha>) p (Ln_rules_to_rule ((r1, a)#rs1)) Undecided =
       approximating_bigstep_fun (simple_matcher, \<alpha>) p (Ln_rules_to_rule ((r2, a)#rs2)) Undecided"
by(simp add: Ln_rules_to_rule_head split: action.split)

theorem compress_Ln_ips_xorrectness: "approximating_bigstep_fun (simple_matcher, \<alpha>) p (Ln_rules_to_rule (compress_Ln_ips rs1)) s = 
      approximating_bigstep_fun (simple_matcher, \<alpha>) p (Ln_rules_to_rule rs1) s"
apply(case_tac s)
 prefer 2
 apply(simp add: Decision_approximating_bigstep_fun)
apply(clarify, thin_tac "s = Undecided")
apply(induction rs1)
 apply(simp)
apply(rename_tac r rs)
apply(case_tac r, simp)
apply(rename_tac m action)
apply(case_tac m)
apply(rename_tac src dst proto extra)
apply(simp only:compress_Ln_ips.simps)
apply(simp del: compress_ips.simps split: option.split)
apply(safe)
  apply(drule_tac \<alpha>=\<alpha> and p=p and proto=proto and extra=extra and dst=dst and a=action in compress_ips_src_None_matching)
  apply(simp add: Ln_rules_to_rule_head Ln_uncompressed_matching)
 apply(drule_tac \<alpha>=\<alpha> and p=p and proto=proto and extra=extra and src=src and a=action in compress_ips_dst_None_matching)
 apply(simp add: Ln_rules_to_rule_head Ln_uncompressed_matching)
apply(simp del: compress_ips.simps)
apply(drule_tac \<alpha>=\<alpha> and p=p and a=action in compress_ips_dst_Some_matching) (*careful about order of src/dst*)
apply(drule_tac \<alpha>=\<alpha> and p=p and a=action in compress_ips_src_Some_matching)
apply(rule approximating_bigstep_fun_Ln_rules_to_rule_step_simultaneously, simp)
apply(rule Ln_uncompressed_matching_src_dst_eq[simplified Ln_uncompressed_matching])
apply(simp_all)
done

(**TODO: compress protocols**)
fun does_I_has_compressed_rules :: "(iptrule_match_Ln_uncompressed \<times> action) list \<Rightarrow> (iptrule_match_Ln_uncompressed \<times> action) list" where
  "does_I_has_compressed_rules [] = []" |
  "does_I_has_compressed_rules (((UncompressedFormattedMatch [] [dst] proto []), a)#rs) =
    does_I_has_compressed_rules rs" |
  "does_I_has_compressed_rules (((UncompressedFormattedMatch [src] [] proto []), a)#rs) =
    does_I_has_compressed_rules rs" |
  "does_I_has_compressed_rules (((UncompressedFormattedMatch [src] [dst] proto []), a)#rs) =
    does_I_has_compressed_rules rs" |
  "does_I_has_compressed_rules (((UncompressedFormattedMatch [] [] proto []), a)#rs) =
    does_I_has_compressed_rules rs" |
  "does_I_has_compressed_rules (r#rs) = r # does_I_has_compressed_rules rs"


fun does_I_has_compressed_prots :: "(iptrule_match_Ln_uncompressed \<times> action) list \<Rightarrow> (iptrule_match_Ln_uncompressed \<times> action) list" where
  "does_I_has_compressed_prots [] = []" |
  "does_I_has_compressed_prots (((UncompressedFormattedMatch src dst [] []), a)#rs) =
    does_I_has_compressed_prots rs"|
  "does_I_has_compressed_prots (((UncompressedFormattedMatch src dst [proto] []), a)#rs) =
    does_I_has_compressed_prots rs"|
  "does_I_has_compressed_prots (r#rs) =
    r # does_I_has_compressed_prots rs"

end

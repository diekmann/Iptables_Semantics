theory Ports_Normalize
imports "IPPortIfaceSpace_Matcher" "../Semantics_Ternary"
        "Primitive_Normalization"
begin



subsection{*Normalizing ports*}

  fun ipt_ports_negation_type_normalize :: "ipt_ports negation_type \<Rightarrow> ipt_ports" where
    "ipt_ports_negation_type_normalize (Pos ps) = ps" |
    "ipt_ports_negation_type_normalize (Neg ps) = br2l (bitrange_invert (l2br ps))"  
  
  
  lemma "ipt_ports_negation_type_normalize (Neg [(0,65535)]) = []" by eval

  declare ipt_ports_negation_type_normalize.simps[simp del]
  
  lemma ipt_ports_negation_type_normalize_correct:
        "matches (ipportiface_matcher, \<alpha>) (negation_type_to_match_expr_f (Src_Ports) ps) a p \<longleftrightarrow>
         matches (ipportiface_matcher, \<alpha>) (Match (Src_Ports (ipt_ports_negation_type_normalize ps))) a p"
        "matches (ipportiface_matcher, \<alpha>) (negation_type_to_match_expr_f (Dst_Ports) ps) a p \<longleftrightarrow>
         matches (ipportiface_matcher, \<alpha>) (Match (Dst_Ports (ipt_ports_negation_type_normalize ps))) a p"
  apply(case_tac [!] ps)
  apply(simp_all add: ipt_ports_negation_type_normalize.simps matches_case_ternaryvalue_tuple
          bunch_of_lemmata_about_matches bool_to_ternary_simps l2br_br2l ports_to_set_bitrange split: ternaryvalue.split)
  done
  
  (* [ [(1,2) \<or> (3,4)]  \<and>  [] ]*)
  text{* @{typ "ipt_ports list \<Rightarrow> ipt_ports"} *}
  definition ipt_ports_andlist_compress :: "('a::len word \<times> 'a::len word) list list \<Rightarrow> ('a::len word \<times> 'a::len word) list" where
    "ipt_ports_andlist_compress pss = br2l (fold (\<lambda>ps accu. (bitrange_intersection (l2br ps) accu)) pss bitrange_UNIV)"
  
  lemma ipt_ports_andlist_compress_correct: "ports_to_set (ipt_ports_andlist_compress pss) = \<Inter> set (map ports_to_set pss)"
    proof -
      { fix accu
        have "ports_to_set (br2l (fold (\<lambda>ps accu. (bitrange_intersection (l2br ps) accu)) pss accu)) = (\<Inter> set (map ports_to_set pss)) \<inter> (ports_to_set (br2l accu))"
          apply(induction pss arbitrary: accu)
           apply(simp_all add: ports_to_set_bitrange l2br_br2l)
          by fast
      }
      from this[of bitrange_UNIV] show ?thesis
        unfolding ipt_ports_andlist_compress_def by(simp add: ports_to_set_bitrange l2br_br2l)
    qed
  
  
  definition ipt_ports_compress :: "ipt_ports negation_type list \<Rightarrow> ipt_ports" where
    "ipt_ports_compress pss = ipt_ports_andlist_compress (map ipt_ports_negation_type_normalize pss)"
  
  
  (*TODO: only for src*)
  lemma ipt_ports_compress_src_correct:
    "matches (ipportiface_matcher, \<alpha>) (alist_and (NegPos_map Src_Ports ms)) a p \<longleftrightarrow> matches (ipportiface_matcher, \<alpha>) (Match (Src_Ports (ipt_ports_compress ms))) a p"
  proof(induction ms)
    case Nil thus ?case by(simp add: ipt_ports_compress_def bunch_of_lemmata_about_matches ipt_ports_andlist_compress_correct)
    next
    case (Cons m ms)
      thus ?case (is ?goal)
      proof(cases m)
        case Pos thus ?goal using Cons.IH
          by(simp add: ipt_ports_compress_def ipt_ports_andlist_compress_correct bunch_of_lemmata_about_matches
              ternary_to_bool_bool_to_ternary ipt_ports_negation_type_normalize.simps)
        next
        case (Neg a)
          thus ?goal using Cons.IH
          apply(simp add: ipt_ports_compress_def ipt_ports_andlist_compress_correct bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary)
          apply(simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps l2br_br2l
                  ports_to_set_bitrange ipt_ports_negation_type_normalize.simps split: ternaryvalue.split)
          done
        qed
  qed
  lemma ipt_ports_compress_dst_correct:
    "matches (ipportiface_matcher, \<alpha>) (alist_and (NegPos_map Dst_Ports ms)) a p \<longleftrightarrow> matches (ipportiface_matcher, \<alpha>) (Match (Dst_Ports (ipt_ports_compress ms))) a p"
  proof(induction ms)
    case Nil thus ?case by(simp add: ipt_ports_compress_def bunch_of_lemmata_about_matches ipt_ports_andlist_compress_correct)
    next
    case (Cons m ms)
      thus ?case (is ?goal)
      proof(cases m)
        case Pos thus ?goal using Cons.IH
          by(simp add: ipt_ports_compress_def ipt_ports_andlist_compress_correct bunch_of_lemmata_about_matches
                ternary_to_bool_bool_to_ternary ipt_ports_negation_type_normalize.simps)
        next
        case (Neg a)
          thus ?goal using Cons.IH
          apply(simp add: ipt_ports_compress_def ipt_ports_andlist_compress_correct bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary)
          apply(simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps l2br_br2l ports_to_set_bitrange
              ipt_ports_negation_type_normalize.simps split: ternaryvalue.split)
          done
        qed
  qed
  
  
  lemma ipt_ports_compress_matches_set: "matches (ipportiface_matcher, \<alpha>) (Match (Src_Ports (ipt_ports_compress ips))) a p \<longleftrightarrow>
         p_sport p \<in> \<Inter> set (map (ports_to_set \<circ> ipt_ports_negation_type_normalize) ips)"
  apply(simp add: ipt_ports_compress_def)
  apply(induction ips)
   apply(simp)
   apply(simp add: ipt_ports_compress_def bunch_of_lemmata_about_matches ipt_ports_andlist_compress_correct)
  apply(rename_tac m ms)
  apply(case_tac m)
   apply(simp add: ipt_ports_andlist_compress_correct bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary ipt_ports_negation_type_normalize.simps)
  apply(simp add: ipt_ports_andlist_compress_correct bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary)
  done
  
  
  (*spliting the primitives: multiport list (a list of disjunction!)*)
  lemma singletonize_SrcDst_Ports: "match_list (ipportiface_matcher, \<alpha>) (map (\<lambda>spt. (MatchAnd (Match (Src_Ports [spt]))) ms) (spts)) a p \<longleftrightarrow>
         matches (ipportiface_matcher, \<alpha>) (MatchAnd (Match (Src_Ports spts)) ms) a p"
         "match_list (ipportiface_matcher, \<alpha>) (map (\<lambda>spt. (MatchAnd (Match (Dst_Ports [spt]))) ms) (dpts)) a p \<longleftrightarrow>
         matches (ipportiface_matcher, \<alpha>) (MatchAnd (Match (Dst_Ports dpts)) ms) a p"
    apply(simp_all add: match_list_matches bunch_of_lemmata_about_matches(1) multiports_disjuction)
  done
  
  
  (*idea:*)
  value "case primitive_extractor (is_Src_Ports, src_ports_sel) m 
          of (spts, rst) \<Rightarrow> map (\<lambda>spt. (MatchAnd (Match (Src_Ports [spt]))) rst) (ipt_ports_compress spts)"
  
  
  text{*Normalizing match expressions such that at most one port will exist in it. Returns a list of match expressions (splits one firewall rule into several rules).*}
  definition normalize_ports_step :: "((common_primitive \<Rightarrow> bool) \<times> (common_primitive \<Rightarrow> ipt_ports)) \<Rightarrow> 
                               (ipt_ports \<Rightarrow> common_primitive) \<Rightarrow>
                               common_primitive match_expr \<Rightarrow> common_primitive match_expr list" where 
    "normalize_ports_step (disc_sel) C  m = (case primitive_extractor (disc_sel) m 
                of (spts, rst) \<Rightarrow> map (\<lambda>spt. (MatchAnd (Match (C [spt]))) rst) (ipt_ports_compress spts))"

  (*TODO: We can use the generalized version. TODO: remove above def, simplify proofs with it*)
  lemma normalize_ports_step_def2:
    "normalize_ports_step disc_sel C m = normalize_primitive_extract disc_sel C (\<lambda>me. map (\<lambda>pt. [pt]) (ipt_ports_compress me)) m"
    apply(simp add: normalize_ports_step_def normalize_primitive_extract_def)
    by(cases "primitive_extractor disc_sel m", simp)
  
  lemma normalize_ports_step_Src: assumes "normalized_match m" shows
        "match_list (ipportiface_matcher, \<alpha>) (normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports m) a p \<longleftrightarrow>
         matches (ipportiface_matcher, \<alpha>) m a p"
         (*apply(simp add: normalize_ports_step_def2,rule normalize_primitive_extract[OF assms wf_disc_sel_common_primitive(1)])*)
    proof -
      obtain as ms where pe: "primitive_extractor (is_Src_Ports, src_ports_sel) m = (as, ms)" by fastforce
      from pe have normalize_ports_step: "normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports m = 
            (map (\<lambda>spt. MatchAnd (Match (Src_Ports [spt])) ms) (ipt_ports_compress as))"
        by(simp add: normalize_ports_step_def)
      from pe  primitive_extractor_correct(1)[OF assms wf_disc_sel_common_primitive(1), where \<gamma>="(ipportiface_matcher, \<alpha>)" and a=a and p=p] have 
        "matches (ipportiface_matcher, \<alpha>) m a p \<longleftrightarrow> 
          (matches (ipportiface_matcher, \<alpha>) (alist_and (NegPos_map Src_Ports as)) a p \<and> matches (ipportiface_matcher, \<alpha>) ms a p)"
      by simp
      also have "... \<longleftrightarrow> match_list (ipportiface_matcher, \<alpha>) (normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports m) a p"
        by(simp add: normalize_ports_step singletonize_SrcDst_Ports(1) bunch_of_lemmata_about_matches(1) ipt_ports_compress_src_correct)
      finally show ?thesis by simp
    qed
  lemma normalize_ports_step_Dst: assumes "normalized_match m" shows
        "match_list (ipportiface_matcher, \<alpha>) (normalize_ports_step (is_Dst_Ports, dst_ports_sel) Dst_Ports m) a p \<longleftrightarrow>
         matches (ipportiface_matcher, \<alpha>) m a p"
    proof -
      obtain as ms where pe: "primitive_extractor (is_Dst_Ports, dst_ports_sel) m = (as, ms)" by fastforce
      from pe have normalize_ports_step: "normalize_ports_step (is_Dst_Ports, dst_ports_sel) Dst_Ports m =
          (map (\<lambda>spt. MatchAnd (Match (Dst_Ports [spt])) ms) (ipt_ports_compress as))"
        by(simp add: normalize_ports_step_def)
      from pe  primitive_extractor_correct(1)[OF assms wf_disc_sel_common_primitive(2), where \<gamma>="(ipportiface_matcher, \<alpha>)" and a=a and p=p] have 
        "matches (ipportiface_matcher, \<alpha>) m a p \<longleftrightarrow>
          (matches (ipportiface_matcher, \<alpha>) (alist_and (NegPos_map Dst_Ports as)) a p \<and> matches (ipportiface_matcher, \<alpha>) ms a p)"
      by simp
      also have "... \<longleftrightarrow> match_list (ipportiface_matcher, \<alpha>) (normalize_ports_step (is_Dst_Ports, dst_ports_sel) Dst_Ports m) a p"
        by(simp add: normalize_ports_step singletonize_SrcDst_Ports(2) bunch_of_lemmata_about_matches(1) ipt_ports_compress_dst_correct)
      finally show ?thesis by simp
    qed
  

  value "normalized_match (MatchAnd (MatchNot (Match (Src_Ports [(1,2)]))) (Match (Src_Ports [(1,2)])))"
  value "normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports (MatchAnd (MatchNot (Match (Src_Ports [(5,9)]))) (Match (Src_Ports [(1,2)])))"

  (*TODO: probably we should optimize away the (Match (Src_Ports [(0, 65535)]))*)
  value "normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports (MatchAnd (MatchNot (Match (Prot (Proto TCP)))) (Match (Prot (ProtoAny))))"
  
  fun normalized_src_ports :: "common_primitive match_expr \<Rightarrow> bool" where
    "normalized_src_ports MatchAny = True" |
    "normalized_src_ports (Match (Src_Ports [])) = True" |
    "normalized_src_ports (Match (Src_Ports [_])) = True" |
    "normalized_src_ports (Match (Src_Ports _)) = False" |
    "normalized_src_ports (Match _) = True" |
    "normalized_src_ports (MatchNot (Match (Src_Ports _))) = False" |
    "normalized_src_ports (MatchAnd m1 m2) = (normalized_src_ports m1 \<and> normalized_src_ports m2)" |
    "normalized_src_ports (MatchNot (MatchAnd _ _)) = False" |
    "normalized_src_ports (MatchNot _) = True"
  
  fun normalized_dst_ports :: "common_primitive match_expr \<Rightarrow> bool" where
    "normalized_dst_ports MatchAny = True" |
    "normalized_dst_ports (Match (Dst_Ports [])) = True" |
    "normalized_dst_ports (Match (Dst_Ports [_])) = True" |
    "normalized_dst_ports (Match (Dst_Ports _)) = False" |
    "normalized_dst_ports (Match _) = True" |
    "normalized_dst_ports (MatchNot (Match (Dst_Ports _))) = False" |
    "normalized_dst_ports (MatchAnd m1 m2) = (normalized_dst_ports m1 \<and> normalized_dst_ports m2)" |
    "normalized_dst_ports (MatchNot (MatchAnd _ _)) = False" |
    "normalized_dst_ports (MatchNot _) = True" 

  lemma normalized_src_ports_def2: "normalized_src_ports ms = normalized_n_primitive (is_Src_Ports, src_ports_sel) (\<lambda>pts. length pts \<le> 1) ms"
    by(induction ms rule: normalized_src_ports.induct, simp_all)
  lemma normalized_dst_ports_def2: "normalized_dst_ports ms = normalized_n_primitive (is_Dst_Ports, dst_ports_sel) (\<lambda>pts. length pts \<le> 1) ms"
    by(induction ms rule: normalized_dst_ports.induct, simp_all)
  
  (*unused? TODO: Move?*)
  lemma normalized_match_MatchNot_D: "normalized_match (MatchNot m) \<Longrightarrow> normalized_match m"
  apply(induction m)
  apply(simp_all)
  done
  
  
  lemma "\<forall>spt \<in> set (ipt_ports_compress spts). normalized_src_ports (Match (Src_Ports [spt]))" by(simp)
  

  lemma normalize_ports_step_src_normalized:
    assumes "normalized_match m"
    shows "\<forall>mn \<in> set (normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports m). normalized_src_ports mn \<and> normalized_match mn"
    proof
      fix mn
      assume assm2: "mn \<in> set (normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports m)"
      obtain pts ms where pts_ms: "primitive_extractor (is_Src_Ports, src_ports_sel) m = (pts, ms)" by fastforce
      from pts_ms have "normalized_match ms" and "\<not> has_disc is_Src_Ports ms"
        using primitive_extractor_correct[OF assms wf_disc_sel_common_primitive(1)] by simp_all
      from assm2 pts_ms have normalize_ports_step_unfolded: "mn \<in> (\<lambda>spt. MatchAnd (Match (Src_Ports [spt])) ms) ` set (ipt_ports_compress pts)"
        unfolding normalize_ports_step_def by force
      with `normalized_match ms` have "normalized_match mn" by fastforce
      from `normalized_match ms` `\<not> has_disc is_Src_Ports ms` have "normalized_src_ports ms"
        by(induction ms rule: normalized_src_ports.induct, simp_all)
      from normalize_ports_step_unfolded this have "normalized_src_ports mn"
      by(induction pts) (fastforce)+
      with `normalized_match mn` show "normalized_src_ports mn \<and> normalized_match mn" by simp
    qed

  (*using the generalized version, we can push through normalized conditions*)
  lemma "normalized_match m \<Longrightarrow> normalized_dst_ports m \<Longrightarrow>
    \<forall>mn \<in> set (normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports m). normalized_src_ports mn \<and> normalized_dst_ports mn \<and> normalized_match mn"
  apply(frule normalize_ports_step_src_normalized)
  apply(simp add: normalized_dst_ports_def2 normalize_ports_step_def2)
  apply(frule(1) normalize_primitive_extract_maintains_normalized[OF _ _ wf_disc_sel_common_primitive(1), where f="(\<lambda>me. map (\<lambda>pt. [pt]) (ipt_ports_compress me))"])
   apply(simp_all)
  done

end

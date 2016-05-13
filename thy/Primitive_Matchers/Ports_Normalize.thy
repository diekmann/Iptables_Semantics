theory Ports_Normalize
imports Common_Primitive_Lemmas
begin



subsection\<open>Normalizing ports\<close>

context
begin

  private fun ipt_ports_negation_type_normalize :: "ipt_ports negation_type \<Rightarrow> ipt_ports" where
    "ipt_ports_negation_type_normalize (Pos ps) = ps" |
    "ipt_ports_negation_type_normalize (Neg ps) = ports_invert ps"  
  
  
  private lemma "ipt_ports_negation_type_normalize (Neg [(0,65535)]) = []" by eval

  declare ipt_ports_negation_type_normalize.simps[simp del]
  
  (*
  private lemma ipt_ports_negation_type_normalize_correct:
        "primitive_matcher_generic \<beta> \<Longrightarrow> 
         matches (\<beta>, \<alpha>) (negation_type_to_match_expr_f (Src_Ports) ps) a p \<longleftrightarrow>
         matches (\<beta>, \<alpha>) (Match (Src_Ports (ipt_ports_negation_type_normalize ps))) a p"
        "primitive_matcher_generic \<beta> \<Longrightarrow> 
         matches (\<beta>, \<alpha>) (negation_type_to_match_expr_f (Dst_Ports) ps) a p \<longleftrightarrow>
         matches (\<beta>, \<alpha>) (Match (Dst_Ports (ipt_ports_negation_type_normalize ps))) a p"
  apply(case_tac [!] ps)
  apply(simp_all add: primitive_matcher_generic.Ports_single primitive_matcher_generic.Ports_single_not)
  apply(simp_all add: ipt_ports_negation_type_normalize.simps ports_invert split: ternaryvalue.split)
  done
  *)
  
  (* [ [(1,2) \<or> (3,4)]  \<and>  [] ]*)
  text\<open>@{typ "ipt_ports list \<Rightarrow> ipt_ports"}\<close>
  private definition ipt_ports_andlist_compress :: "('a::len word \<times> 'a::len word) list list \<Rightarrow> ('a::len word \<times> 'a::len word) list" where
    "ipt_ports_andlist_compress pss = br2l (fold (\<lambda>ps accu. (wordinterval_intersection (l2br ps) accu)) pss wordinterval_UNIV)"
  
  private lemma ipt_ports_andlist_compress_correct: "ports_to_set (ipt_ports_andlist_compress pss) = \<Inter> set (map ports_to_set pss)"
    proof -
      { fix accu
        have "ports_to_set (br2l (fold (\<lambda>ps accu. (wordinterval_intersection (l2br ps) accu)) pss accu)) = (\<Inter> set (map ports_to_set pss)) \<inter> (ports_to_set (br2l accu))"
          apply(induction pss arbitrary: accu)
           apply(simp_all add: ports_to_set_wordinterval l2br_br2l)
          by fast
      }
      from this[of wordinterval_UNIV] show ?thesis
        unfolding ipt_ports_andlist_compress_def by(simp add: ports_to_set_wordinterval l2br_br2l)
    qed
  
  
  definition ipt_ports_compress :: "ipt_ports negation_type list \<Rightarrow> ipt_ports" where
    "ipt_ports_compress pss = ipt_ports_andlist_compress (map ipt_ports_negation_type_normalize pss)"
  
  
  (*only for src*)
  private lemma ipt_ports_compress_src_correct:
  fixes p :: "('i::len, 'a) simple_packet_scheme"
  assumes generic: "primitive_matcher_generic \<beta>"
  shows "matches (\<beta>, \<alpha>) (alist_and (NegPos_map Src_Ports ms)) a p \<longleftrightarrow> 
         matches (\<beta>, \<alpha>) (Match (Src_Ports (ipt_ports_compress ms))) a p"
  proof(induction ms)
    case Nil with generic show ?case
      unfolding primitive_matcher_generic.Ports_single[OF generic]
      by(simp add: ipt_ports_compress_def bunch_of_lemmata_about_matches ipt_ports_andlist_compress_correct)
    next
    case (Cons m ms)
      thus ?case
      proof(cases m)
        case Pos thus ?thesis using Cons.IH primitive_matcher_generic.Ports_single[OF generic]
          by(simp add: ipt_ports_compress_def ipt_ports_andlist_compress_correct bunch_of_lemmata_about_matches
                ipt_ports_negation_type_normalize.simps)
        next
        case (Neg a)
          thus ?thesis using Cons.IH generic primitive_matcher_generic.Ports_single_not[where p = p] primitive_matcher_generic.Ports_single[where p = p]
          apply(simp add: ipt_ports_compress_def ipt_ports_andlist_compress_correct
                          bunch_of_lemmata_about_matches[where p = p] ternary_to_bool_bool_to_ternary)
          apply(simp add: ports_invert ipt_ports_negation_type_normalize.simps)
          done
        qed
  qed
  (*only for dst*)
  private lemma ipt_ports_compress_dst_correct:
  assumes generic: "primitive_matcher_generic \<beta>"
  shows "matches (\<beta>, \<alpha>) (alist_and (NegPos_map Dst_Ports ms)) a p \<longleftrightarrow>
         matches (\<beta>, \<alpha>) (Match (Dst_Ports (ipt_ports_compress ms))) a p"
  proof(induction ms)
    case Nil thus ?case
      unfolding primitive_matcher_generic.Ports_single[OF generic]
      by(simp add: ipt_ports_compress_def bunch_of_lemmata_about_matches ipt_ports_andlist_compress_correct)
    next
    case (Cons m ms)
      thus ?case
      proof(cases m)
        case Pos thus ?thesis using Cons.IH primitive_matcher_generic.Ports_single[OF generic]
          by(simp add: ipt_ports_compress_def ipt_ports_andlist_compress_correct bunch_of_lemmata_about_matches
                ipt_ports_negation_type_normalize.simps)
        next
        case (Neg a)
          thus ?thesis using Cons.IH primitive_matcher_generic.Ports_single[OF generic] primitive_matcher_generic.Ports_single_not[OF generic]
          apply(simp add: ipt_ports_compress_def ipt_ports_andlist_compress_correct
                          bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary)
          apply(simp add: ports_invert ipt_ports_negation_type_normalize.simps)
          done
        qed
  qed
  
  (*
  private lemma ipt_ports_compress_matches_set: "primitive_matcher_generic \<beta> \<Longrightarrow>
         matches (\<beta>, \<alpha>) (Match (Src_Ports (ipt_ports_compress ips))) a p \<longleftrightarrow>
         p_sport p \<in> \<Inter> set (map (ports_to_set \<circ> ipt_ports_negation_type_normalize) ips)"
  apply(simp add: ipt_ports_compress_def)
  apply(induction ips)
   apply(simp)
   apply(simp add: ipt_ports_compress_def bunch_of_lemmata_about_matches
                   ipt_ports_andlist_compress_correct primitive_matcher_generic_def; fail)
  apply(rename_tac m ms)
  apply(case_tac m)
   apply(simp add: primitive_matcher_generic.Ports_single ipt_ports_andlist_compress_correct; fail)
  apply(simp add: primitive_matcher_generic.Ports_single ipt_ports_andlist_compress_correct; fail)
  done
  *)
  (*
  (*spliting the primitives: multiport list (a list of disjunction!)*)
  private lemma singletonize_SrcDst_Ports:
      "(*primitive_matcher_generic \<beta> \<Longrightarrow>  multiports_disjuction TODO *)
       match_list (common_matcher, \<alpha>) (map (\<lambda>spt. (MatchAnd (Match (Src_Ports [spt]))) ms) (spts)) a p \<longleftrightarrow>
       matches (common_matcher, \<alpha>) (MatchAnd (Match (Src_Ports spts)) ms) a p"
      "match_list (common_matcher, \<alpha>) (map (\<lambda>spt. (MatchAnd (Match (Dst_Ports [spt]))) ms) (dpts)) a p \<longleftrightarrow>
       matches (common_matcher, \<alpha>) (MatchAnd (Match (Dst_Ports dpts)) ms) a p"
    apply(simp_all add: match_list_matches bunch_of_lemmata_about_matches(1) multiports_disjuction)
  done
  *)
  
  
  (*idea:*)
  value "case primitive_extractor (is_Src_Ports, src_ports_sel) m 
          of (spts, rst) \<Rightarrow> map (\<lambda>spt. (MatchAnd (Match (Src_Ports [spt]))) rst) (ipt_ports_compress spts)"
  
  
  text\<open>Normalizing match expressions such that at most one port will exist in it. Returns a list of match expressions (splits one firewall rule into several rules).\<close>
  definition normalize_ports_step :: "((common_primitive \<Rightarrow> bool) \<times> (common_primitive \<Rightarrow> ipt_ports)) \<Rightarrow> 
                               (ipt_ports \<Rightarrow> common_primitive) \<Rightarrow>
                               common_primitive match_expr \<Rightarrow> common_primitive match_expr list" where 
    "normalize_ports_step (disc_sel) C = normalize_primitive_extract disc_sel C (\<lambda>me. map (\<lambda>pt. [pt]) (ipt_ports_compress me))"

  definition normalize_src_ports :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr list" where
    "normalize_src_ports = normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports"  
  definition normalize_dst_ports :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr list" where
    "normalize_dst_ports = normalize_ports_step (is_Dst_Ports, dst_ports_sel) Dst_Ports"

  lemma normalize_src_ports: assumes generic: "primitive_matcher_generic \<beta>" and n: "normalized_nnf_match m" shows
        "match_list (\<beta>, \<alpha>) (normalize_src_ports m) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
    proof -
      { fix ml
        have "match_list (\<beta>, \<alpha>) (map (Match \<circ> Src_Ports) (map (\<lambda>pt. [pt]) (ipt_ports_compress ml))) a p =
         matches (\<beta>, \<alpha>) (alist_and (NegPos_map Src_Ports ml)) a p"
         using ipt_ports_compress_src_correct[OF generic] primitive_matcher_generic.multiports_disjuction[OF generic]
         by(simp add: match_list_matches)
      } with normalize_primitive_extract[OF n wf_disc_sel_common_primitive(1), where \<gamma>="(\<beta>, \<alpha>)"]
      show ?thesis
        unfolding normalize_src_ports_def normalize_ports_step_def by simp
    qed

    lemma normalize_dst_ports: assumes generic: "primitive_matcher_generic \<beta>" and n: "normalized_nnf_match m" shows
        "match_list (\<beta>, \<alpha>) (normalize_dst_ports m) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
    proof -
      { fix ml
        have "match_list (\<beta>, \<alpha>) (map (Match \<circ> Dst_Ports) (map (\<lambda>pt. [pt]) (ipt_ports_compress ml))) a p =
         matches (\<beta>, \<alpha>) (alist_and (NegPos_map Dst_Ports ml)) a p"
         using ipt_ports_compress_dst_correct[OF generic] primitive_matcher_generic.multiports_disjuction[OF generic]
         by(simp add: match_list_matches)
      } with normalize_primitive_extract[OF n wf_disc_sel_common_primitive(2), where \<gamma>="(\<beta>, \<alpha>)"]
      show ?thesis
        unfolding normalize_dst_ports_def normalize_ports_step_def by simp
    qed


  value "normalized_nnf_match (MatchAnd (MatchNot (Match (Src_Ports [(1,2)]))) (Match (Src_Ports [(1,2)])))"
  value "normalize_src_ports (MatchAnd (MatchNot (Match (Src_Ports [(5,9)]))) (Match (Src_Ports [(1,2)])))"

  (*probably we should optimize away the (Match (Src_Ports [(0, 65535)]))*)
  value "normalize_src_ports (MatchAnd (MatchNot (Match (Prot (Proto TCP)))) (Match (Prot (ProtoAny))))"
  
  fun normalized_src_ports :: "common_primitive match_expr \<Rightarrow> bool" where
    "normalized_src_ports MatchAny = True" |
    "normalized_src_ports (Match (Src_Ports [])) = True" |
    "normalized_src_ports (Match (Src_Ports [_])) = True" |
    "normalized_src_ports (Match (Src_Ports _)) = False" |
    "normalized_src_ports (Match _) = True" |
    "normalized_src_ports (MatchNot (Match (Src_Ports _))) = False" |
    "normalized_src_ports (MatchNot (Match _)) = True" |
    "normalized_src_ports (MatchAnd m1 m2) = (normalized_src_ports m1 \<and> normalized_src_ports m2)" |
    "normalized_src_ports (MatchNot (MatchAnd _ _)) = False" |
    "normalized_src_ports (MatchNot (MatchNot _)) = False" |
    "normalized_src_ports (MatchNot MatchAny) = True"
  
  fun normalized_dst_ports :: "common_primitive match_expr \<Rightarrow> bool" where
    "normalized_dst_ports MatchAny = True" |
    "normalized_dst_ports (Match (Dst_Ports [])) = True" |
    "normalized_dst_ports (Match (Dst_Ports [_])) = True" |
    "normalized_dst_ports (Match (Dst_Ports _)) = False" |
    "normalized_dst_ports (Match _) = True" |
    "normalized_dst_ports (MatchNot (Match (Dst_Ports _))) = False" |
    "normalized_dst_ports (MatchNot (Match _)) = True" |
    "normalized_dst_ports (MatchAnd m1 m2) = (normalized_dst_ports m1 \<and> normalized_dst_ports m2)" |
    "normalized_dst_ports (MatchNot (MatchAnd _ _)) = False" |
    "normalized_dst_ports (MatchNot (MatchNot _)) = False" |
    "normalized_dst_ports (MatchNot MatchAny) = True" 

  lemma normalized_src_ports_def2: "normalized_src_ports ms = normalized_n_primitive (is_Src_Ports, src_ports_sel) (\<lambda>pts. length pts \<le> 1) ms"
    by(induction ms rule: normalized_src_ports.induct, simp_all)
  lemma normalized_dst_ports_def2: "normalized_dst_ports ms = normalized_n_primitive (is_Dst_Ports, dst_ports_sel) (\<lambda>pts. length pts \<le> 1) ms"
    by(induction ms rule: normalized_dst_ports.induct, simp_all)
  
  
  private lemma "\<forall>spt \<in> set (ipt_ports_compress spts). normalized_src_ports (Match (Src_Ports [spt]))" by(simp)
  

  lemma normalize_src_ports_normalized_n_primitive: "normalized_nnf_match m \<Longrightarrow> 
      \<forall>m' \<in> set (normalize_src_ports m). normalized_src_ports m'"
  unfolding normalize_src_ports_def normalize_ports_step_def
  unfolding normalized_src_ports_def2
  apply(rule normalize_primitive_extract_normalizes_n_primitive[OF _ wf_disc_sel_common_primitive(1)])
   by(simp_all)


  lemma "normalized_nnf_match m \<Longrightarrow>
      \<forall>m' \<in> set (normalize_src_ports m). normalized_src_ports m' \<and> normalized_nnf_match m'"
  apply(intro ballI, rename_tac mn)
  apply(rule conjI)
   apply(simp add: normalize_src_ports_normalized_n_primitive)
  unfolding normalize_src_ports_def normalize_ports_step_def
  unfolding normalized_dst_ports_def2
   by(auto dest: normalize_primitive_extract_preserves_nnf_normalized[OF _ wf_disc_sel_common_primitive(1)])

  lemma normalize_dst_ports_normalized_n_primitive: "normalized_nnf_match m \<Longrightarrow> 
      \<forall>m' \<in> set (normalize_dst_ports m). normalized_dst_ports m'"
  unfolding normalize_dst_ports_def normalize_ports_step_def
  unfolding normalized_dst_ports_def2
  apply(rule normalize_primitive_extract_normalizes_n_primitive[OF _ wf_disc_sel_common_primitive(2)])
   by(simp_all)

  (*using the generalized version, we can push through normalized conditions*)
  lemma "normalized_nnf_match m \<Longrightarrow> normalized_dst_ports m \<Longrightarrow>
    \<forall>mn \<in> set (normalize_src_ports m). normalized_dst_ports mn"
  unfolding normalized_dst_ports_def2 normalize_src_ports_def normalize_ports_step_def
  apply(frule(1) normalize_primitive_extract_preserves_unrelated_normalized_n_primitive[OF _ _ wf_disc_sel_common_primitive(1), where f="(\<lambda>me. map (\<lambda>pt. [pt]) (ipt_ports_compress me))"])
   apply(simp_all)
  done

end
end

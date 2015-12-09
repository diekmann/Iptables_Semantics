theory Interfaces_Normalize
imports Common_Primitive_Lemmas
        Ipassmt
begin


  definition compress_normalize_primitive :: "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow>
                                              ('b negation_type list \<Rightarrow> ('b list \<times> 'b list) option) \<Rightarrow> 
                                              'a match_expr \<Rightarrow> 'a match_expr option" where 
    "compress_normalize_primitive disc_sel C f m \<equiv> (case primitive_extractor disc_sel m of (as, rst) \<Rightarrow>
      (map_option (\<lambda>(as_pos, as_neg). MatchAnd
                                       (alist_and (NegPos_map C ((map Pos as_pos)@(map Neg as_neg))))
                                       rst
                  ) (f as)))"



  lemma compress_normalize_primitive_nnf: "wf_disc_sel disc_sel C \<Longrightarrow> 
      normalized_nnf_match m \<Longrightarrow> compress_normalize_primitive disc_sel C f m = Some m' \<Longrightarrow>
    normalized_nnf_match m'"
    apply(case_tac "primitive_extractor disc_sel m")
    apply(simp add: compress_normalize_primitive_def)
    apply(clarify)
    apply (simp add: normalized_nnf_match_alist_and)
    apply(cases disc_sel, simp)
    using primitive_extractor_correct(2) by blast


  lemma compress_normalize_primitive_not_introduces_C:
    assumes notdisc: "\<not> has_disc disc m"
        and wf: "wf_disc_sel (disc,sel) C"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_primitive (disc,sel) C f m = Some m'"
        and f_preserves: "\<And>as_pos as_neg. f [] = Some (as_pos, as_neg) \<Longrightarrow> as_pos = [] \<and> as_neg = []"
     shows "\<not> has_disc disc m'"
   proof -
        obtain as ms where asms: "primitive_extractor (disc, sel) m = (as, ms)" by fastforce
        from notdisc primitive_extractor_correct(4)[OF nm wf asms] have 1: "\<not> has_disc disc ms" by simp
        from notdisc primitive_extractor_correct(7)[OF nm wf asms] have 2: "as = [] \<and> ms = m" by simp
        from 1 2 some show ?thesis by(auto dest: f_preserves simp add: compress_normalize_primitive_def asms)
   qed

  lemma compress_normalize_primitive_not_introduces_C_negated:
    assumes notdisc: "\<not> has_disc_negated disc False m"
        and wf: "wf_disc_sel (disc,sel) C"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_primitive (disc,sel) C f m = Some m'"
        and f_preserves: "\<And>as as_pos as_neg. f as = Some (as_pos, as_neg) \<Longrightarrow> getNeg as = [] \<Longrightarrow> as_neg = []"
     shows "\<not> has_disc_negated disc False m'"
   proof -
        obtain as ms where asms: "primitive_extractor (disc,sel) m = (as, ms)" by fastforce
        from notdisc primitive_extractor_correct(6)[OF nm wf asms] have 1: "\<not> has_disc_negated disc False ms" by simp
        from asms notdisc has_disc_negated_primitive_extractor[OF nm, where disc=disc and sel=sel] have
          "\<forall>a. Neg a \<notin> set as" by(simp)
        hence "getNeg as = []" by (meson NegPos_set(5) image_subset_iff last_in_set)
        with f_preserves have f_preserves': "\<And>as_pos as_neg. f as = Some (as_pos, as_neg) \<Longrightarrow> as_neg = []" by simp
        { fix as
          have "\<not> has_disc_negated is_Iiface False (alist_and (NegPos_map IIface (map Pos as)))"
            by(simp add: has_disc_negated_alist_and NegPos_map_map_Pos negation_type_to_match_expr_simps)  
        }
        with 1 have "\<And> a b.\<not> has_disc_negated disc False (MatchAnd (alist_and (NegPos_map C (map Pos a))) ms)"
          by(simp add: has_disc_negated_alist_and NegPos_map_map_Pos negation_type_to_match_expr_simps)
        with some show ?thesis by(auto dest: f_preserves' simp add: compress_normalize_primitive_def asms)
   qed




  lemma compress_normalize_primitive_Some:
  assumes normalized: "normalized_nnf_match m"
      and wf: "wf_disc_sel (disc,sel) C"
      and some: "compress_normalize_primitive (disc,sel) C f m = Some m'"
      and f_correct: "\<And>as as_pos as_neg. f as = Some (as_pos, as_neg) \<Longrightarrow>
            matches \<gamma> (alist_and (NegPos_map C ((map Pos as_pos)@(map Neg as_neg)))) a p \<longleftrightarrow>
            matches \<gamma> (alist_and (NegPos_map C as)) a p"
    shows "matches \<gamma> m' a p \<longleftrightarrow> matches \<gamma> m a p"
    using some
    apply(simp add: compress_normalize_primitive_def)
    apply(case_tac "primitive_extractor (disc,sel) m")
    apply(rename_tac as rst, simp)
    apply(drule primitive_extractor_correct(1)[OF normalized wf, where \<gamma>=\<gamma> and a=a and p=p])
    apply(elim exE conjE)
    apply(drule f_correct)
    by (meson alist_and_append bunch_of_lemmata_about_matches(1))
    

  lemma compress_normalize_primitive_None:
  assumes normalized: "normalized_nnf_match m"
      and wf: "wf_disc_sel (disc,sel) C"
      and none: "compress_normalize_primitive (disc,sel) C f m = None"
      and f_correct: "\<And>as. f as = None \<Longrightarrow> \<not> matches \<gamma> (alist_and (NegPos_map C as)) a p"
    shows "\<not> matches \<gamma> m a p"
    using none
    apply(simp add: compress_normalize_primitive_def)
    apply(case_tac "primitive_extractor (disc, sel) m")
    apply(auto dest: primitive_extractor_correct(1)[OF assms(1) wf] f_correct)
    done



  (* only for arbitrary discs that do not match C*)
  lemma compress_normalize_primitive_hasdisc:
    assumes am: "\<not> has_disc disc2 m"
        and wf: "wf_disc_sel (disc,sel) C"
        and disc: "(\<forall>a. \<not> disc2 (C a))"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_primitive (disc,sel) C f m = Some m'"
     shows "normalized_nnf_match m' \<and> \<not> has_disc disc2 m'"
   proof -
        from compress_normalize_primitive_nnf[OF wf nm some] have goal1: "normalized_nnf_match m'" .
        obtain as ms where asms: "primitive_extractor (disc, sel) m = (as, ms)" by fastforce
        from am primitive_extractor_correct(4)[OF nm wf asms] have 1: "\<not> has_disc disc2 ms" by simp
        { fix is_pos is_neg
          from disc have x1: "\<not> has_disc disc2 (alist_and (NegPos_map C (map Pos is_pos)))"
            by(simp add: has_disc_alist_and NegPos_map_map_Pos negation_type_to_match_expr_simps)
          from disc have x2: "\<not> has_disc disc2 (alist_and (NegPos_map C (map Neg is_neg)))"
            by(simp add: has_disc_alist_and NegPos_map_map_Neg negation_type_to_match_expr_simps)
          from x1 x2 have "\<not> has_disc disc2 (alist_and (NegPos_map C (map Pos is_pos @ map Neg is_neg)))"
            apply(simp add: NegPos_map_append has_disc_alist_and) by blast
        }
        with some have "\<not> has_disc disc2 m'"
          apply(simp add: compress_normalize_primitive_def asms)
          apply(elim exE conjE)
          using 1 by force
        with goal1 show ?thesis by simp
   qed
  lemma compress_normalize_primitive_hasdisc_negated:
    assumes am: "\<not> has_disc_negated disc2 neg m"
        and wf: "wf_disc_sel (disc,sel) C"
        and disc: "(\<forall>a. \<not> disc2 (C a))"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_primitive (disc,sel) C f m = Some m'"
     shows "normalized_nnf_match m' \<and> \<not> has_disc_negated disc2 neg m'"
   proof -
        from compress_normalize_primitive_nnf[OF wf nm some] have goal1: "normalized_nnf_match m'" .
        obtain as ms where asms: "primitive_extractor (disc, sel) m = (as, ms)" by fastforce
        from am primitive_extractor_correct(6)[OF nm wf asms] have 1: "\<not> has_disc_negated disc2 neg ms" by simp
        { fix is_pos is_neg
          from disc have x1: "\<not> has_disc_negated disc2 neg (alist_and (NegPos_map C (map Pos is_pos)))"
            by(simp add: has_disc_negated_alist_and NegPos_map_map_Pos negation_type_to_match_expr_simps)
          from disc have x2: "\<not> has_disc_negated disc2 neg (alist_and (NegPos_map C (map Neg is_neg)))"
            by(simp add: has_disc_negated_alist_and NegPos_map_map_Neg negation_type_to_match_expr_simps)
          from x1 x2 have "\<not> has_disc_negated disc2 neg (alist_and (NegPos_map C (map Pos is_pos @ map Neg is_neg)))"
            apply(simp add: NegPos_map_append has_disc_negated_alist_and) by blast
        }
        with some have "\<not> has_disc_negated disc2 neg m'"
          apply(simp add: compress_normalize_primitive_def asms)
          apply(elim exE conjE)
          using 1 by force
        with goal1 show ?thesis by simp
   qed


  thm normalize_primitive_extract_preserves_unrelated_normalized_n_primitive (*is similar*)
  lemma compress_normalize_primitve_preserves_normalized_n_primitive:
    assumes am: "normalized_n_primitive (disc2, sel2) P m"
        and wf: "wf_disc_sel (disc,sel) C"
        and disc: "(\<forall>a. \<not> disc2 (C a))"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_primitive (disc,sel) C f m = Some m'"
     shows "normalized_nnf_match m' \<and> normalized_n_primitive (disc2, sel2) P m'"
   proof -
        from compress_normalize_primitive_nnf[OF wf nm some] have goal1: "normalized_nnf_match m'" .
        obtain as ms where asms: "primitive_extractor (disc, sel) m = (as, ms)" by fastforce
        from am primitive_extractor_correct[OF nm wf asms] have 1: "normalized_n_primitive (disc2, sel2) P ms" by fast
        { fix iss
          from disc have "normalized_n_primitive (disc2, sel2) P (alist_and (NegPos_map C iss))"
            apply(induction iss)
             apply(simp_all)
            apply(rename_tac i iss, case_tac i)
             apply(simp_all)
            done
        }
        with some have "normalized_n_primitive (disc2, sel2) P m'"
          apply(simp add: compress_normalize_primitive_def asms)
          apply(elim exE conjE)
          using 1 by force
        with goal1 show ?thesis by simp
   qed
  

subsection{*Optimizing interfaces in match expressions*}

  (*TODO a generic primitive optimization function and a separate file for such things*)

  (*returns: (list of positive interfaces \<times> a list of negated interfaces)
    it matches the conjunction of both
    None if the expression cannot match*)
  definition compress_interfaces :: "iface negation_type list \<Rightarrow> (iface list \<times> iface list) option" where
    "compress_interfaces ifces \<equiv> case (compress_pos_interfaces (getPos ifces))
        of None \<Rightarrow> None
        |  Some i \<Rightarrow> if \<exists>negated_ifce \<in> set (getNeg ifces). iface_subset i negated_ifce then None else Some ((if i = ifaceAny then [] else [i]), getNeg ifces)"

term map_option
term option_map (*l4v*)

  lemma compress_interfaces_None: "compress_interfaces ifces = None \<Longrightarrow> \<not> matches (common_matcher, \<alpha>) (alist_and (NegPos_map IIface ifces)) a p"
    apply(simp add: compress_interfaces_def)
    apply(simp add: nt_match_list_matches[symmetric] nt_match_list_simp)
    apply(simp add: NegPos_map_simps match_simplematcher_Iface match_simplematcher_Iface_not)
    apply(case_tac "compress_pos_interfaces (getPos ifces)")
     apply(simp_all)
     apply(drule_tac p_i="p_iiface p" in compress_pos_interfaces_None)
     apply(simp; fail)
    apply(drule_tac p_i="p_iiface p" in compress_pos_interfaces_Some)
    apply(simp split:split_if_asm)
    using iface_subset by blast

  lemma compress_interfaces_Some: "compress_interfaces ifces = Some (i_pos, i_neg) \<Longrightarrow>
    matches (common_matcher, \<alpha>) (alist_and (NegPos_map IIface ((map Pos i_pos)@(map Neg i_neg)))) a p \<longleftrightarrow>
    matches (common_matcher, \<alpha>) (alist_and (NegPos_map IIface ifces)) a p"
    apply(simp add: compress_interfaces_def)
    apply(simp add: bunch_of_lemmata_about_matches(1) alist_and_append NegPos_map_append)
    apply(simp add: nt_match_list_matches[symmetric] nt_match_list_simp)
    apply(simp add: NegPos_map_simps match_simplematcher_Iface match_simplematcher_Iface_not)
    apply(case_tac "compress_pos_interfaces (getPos ifces)")
     apply(simp_all)
    apply(drule_tac p_i="p_iiface p" in compress_pos_interfaces_Some)
    apply(simp split:split_if_asm)
     using match_ifaceAny apply blast
    by force

  
  definition compress_normalize_interfaces :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr option" where 
    "compress_normalize_interfaces m \<equiv> compress_normalize_primitive (is_Iiface, iiface_sel) IIface compress_interfaces m"

  lemma compress_normalize_interfaces_Some:
  assumes "normalized_nnf_match m" and "compress_normalize_interfaces m = Some m'"
    shows "matches (common_matcher, \<alpha>) m' a p \<longleftrightarrow> matches (common_matcher, \<alpha>) m a p"
    apply(rule compress_normalize_primitive_Some[OF assms(1) wf_disc_sel_common_primitive(5)])
     using assms(2) apply(simp add: compress_normalize_interfaces_def; fail)
    using compress_interfaces_Some by simp

  lemma compress_normalize_interfaces_None:
  assumes "normalized_nnf_match m" and "compress_normalize_interfaces m = None"
    shows "\<not> matches (common_matcher, \<alpha>) m a p"
    apply(rule compress_normalize_primitive_None[OF assms(1) wf_disc_sel_common_primitive(5)])
     using assms(2) apply(simp add: compress_normalize_interfaces_def; fail)
    using compress_interfaces_None by simp

  lemma compress_normalize_interfaces_nnf: "normalized_nnf_match m \<Longrightarrow> compress_normalize_interfaces m = Some m' \<Longrightarrow>
      normalized_nnf_match m'"
    unfolding compress_normalize_interfaces_def
    using compress_normalize_primitive_nnf[OF wf_disc_sel_common_primitive(5)] by blast
 
  lemma compress_normalize_interfaces_not_introduces_Iiface:
    "\<not> has_disc is_Iiface m \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_interfaces m = Some m' \<Longrightarrow>
     \<not> has_disc is_Iiface m'"
      apply(simp add: compress_normalize_interfaces_def)
      apply(drule compress_normalize_primitive_not_introduces_C[where m=m])
          apply(simp_all add: wf_disc_sel_common_primitive(5))
      by(simp add: compress_interfaces_def)

  lemma compress_normalize_interfaces_not_introduces_Iiface_negated:
    assumes notdisc: "\<not> has_disc_negated is_Iiface False m"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_interfaces m = Some m'"
     shows "\<not> has_disc_negated is_Iiface False m'"
     apply(rule compress_normalize_primitive_not_introduces_C_negated[OF notdisc wf_disc_sel_common_primitive(5) nm])
     using some apply(simp add: compress_normalize_interfaces_def)
     by(simp add: compress_interfaces_def split: option.split_asm)


  (* only for arbitrary discs that do not match Iiface*)
  lemma compress_normalize_interfaces_hasdisc:
    "\<not> has_disc disc m \<Longrightarrow> (\<forall>a. \<not> disc (IIface a)) \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_interfaces m = Some m' \<Longrightarrow>
     normalized_nnf_match m' \<and> \<not> has_disc disc m'"
     unfolding compress_normalize_interfaces_def
     using compress_normalize_primitive_hasdisc[OF _ wf_disc_sel_common_primitive(5)] by blast

   (* only for arbitrary discs that do not match Iiface*)
  lemma compress_normalize_interfaces_hasdisc_negated:
    "\<not> has_disc_negated disc neg m \<Longrightarrow> (\<forall>a. \<not> disc (IIface a)) \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_interfaces m = Some m' \<Longrightarrow>
     normalized_nnf_match m' \<and> \<not> has_disc_negated disc neg m'"
     unfolding compress_normalize_interfaces_def
     using compress_normalize_primitive_hasdisc_negated[OF _ wf_disc_sel_common_primitive(5)] by blast


  lemma compress_normalize_interfaces_preserves_normalized_n_primitive:
    "normalized_n_primitive (disc, sel) P m \<Longrightarrow> (\<forall>a. \<not> disc (IIface a)) \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_interfaces m = Some m' \<Longrightarrow>
     normalized_nnf_match m' \<and> normalized_n_primitive (disc, sel) P m'"
     unfolding compress_normalize_interfaces_def
   using compress_normalize_primitve_preserves_normalized_n_primitive[OF _ wf_disc_sel_common_primitive(5)] by blast
  

  value[code] "compress_normalize_interfaces 
    (MatchAnd (MatchAnd (MatchAnd (Match (IIface (Iface ''eth+''))) (MatchNot (Match (IIface (Iface ''eth4''))))) (Match (IIface (Iface ''eth1''))))
              (Match (Prot (Proto TCP))))"
    
  value[code] "compress_normalize_interfaces MatchAny"

end
theory Interfaces_Normalize
imports Common_Primitive_Lemmas
begin



subsection\<open>Optimizing interfaces in match expressions\<close>

  (*returns: (list of positive interfaces \<times> a list of negated interfaces)
    it matches the conjunction of both
    None if the expression cannot match*)
  definition compress_interfaces :: "iface negation_type list \<Rightarrow> (iface list \<times> iface list) option" where
    "compress_interfaces ifces \<equiv> case (compress_pos_interfaces (getPos ifces))
        of None \<Rightarrow> None
        |  Some i \<Rightarrow> if
                       \<exists>negated_ifce \<in> set (getNeg ifces). iface_subset i negated_ifce
                     then
                       None
                     else if
                        \<not> iface_is_wildcard i
                      then
                        Some ([i], [])
                      else
                       Some ((if i = ifaceAny then [] else [i]), getNeg ifces)"


context
begin
  private lemma compress_interfaces_None:
    assumes generic: "primitive_matcher_generic \<beta>"
    shows   
      "compress_interfaces ifces = None \<Longrightarrow> \<not> matches (\<beta>, \<alpha>) (alist_and (NegPos_map IIface ifces)) a p"
      "compress_interfaces ifces = None \<Longrightarrow> \<not> matches (\<beta>, \<alpha>) (alist_and (NegPos_map OIface ifces)) a p"
      apply(simp_all add: compress_interfaces_def)
      apply(simp_all add: nt_match_list_matches[symmetric] nt_match_list_simp)
      apply(simp_all add: NegPos_map_simps primitive_matcher_generic.Iface_single[OF generic]
                          primitive_matcher_generic.Iface_single_not[OF generic])
      apply(case_tac [!] "compress_pos_interfaces (getPos ifces)")
        apply(simp_all)
        apply(drule_tac p_i="p_iiface p" in compress_pos_interfaces_None)
        apply(simp; fail)
       apply(drule_tac p_i="p_iiface p" in compress_pos_interfaces_Some)
       apply(simp split:if_split_asm)
       using iface_subset apply blast
       apply(drule_tac p_i="p_oiface p" in compress_pos_interfaces_None)
       apply(simp; fail)
      apply(drule_tac p_i="p_oiface p" in compress_pos_interfaces_Some)
      apply(simp split:if_split_asm)
      using iface_subset by blast
  
  private lemma compress_interfaces_Some: 
    assumes generic: "primitive_matcher_generic \<beta>"
    shows 
      "compress_interfaces ifces = Some (i_pos, i_neg) \<Longrightarrow>
        matches (\<beta>, \<alpha>) (alist_and (NegPos_map IIface ((map Pos i_pos)@(map Neg i_neg)))) a p \<longleftrightarrow>
        matches (\<beta>, \<alpha>) (alist_and (NegPos_map IIface ifces)) a p"
      "compress_interfaces ifces = Some (i_pos, i_neg) \<Longrightarrow>
        matches (\<beta>, \<alpha>) (alist_and (NegPos_map OIface ((map Pos i_pos)@(map Neg i_neg)))) a p \<longleftrightarrow>
        matches (\<beta>, \<alpha>) (alist_and (NegPos_map OIface ifces)) a p"
      apply(simp_all add: compress_interfaces_def)
      apply(simp_all add: bunch_of_lemmata_about_matches(1) alist_and_append NegPos_map_append)
      apply(simp_all add: nt_match_list_matches[symmetric] nt_match_list_simp)
      apply(simp_all add: NegPos_map_simps primitive_matcher_generic.Iface_single[OF generic]
                          primitive_matcher_generic.Iface_single_not[OF generic])
      apply(case_tac [!] "compress_pos_interfaces (getPos ifces)")
         apply(simp_all)
       apply(drule_tac p_i="p_iiface p" in compress_pos_interfaces_Some)
       apply(simp split:if_split_asm)
         using iface_is_wildcard_def iface_subset match_iface_case_nowildcard apply fastforce
        using match_ifaceAny apply blast
       apply force
      apply(drule_tac p_i="p_oiface p" in compress_pos_interfaces_Some)
      apply(simp split:if_split_asm)
        using iface_is_wildcard_def iface_subset match_iface_case_nowildcard apply fastforce
       using match_ifaceAny apply blast
      by force

  
  definition compress_normalize_input_interfaces :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr option" where 
    "compress_normalize_input_interfaces m \<equiv> compress_normalize_primitive (is_Iiface, iiface_sel) IIface compress_interfaces m"

  lemma compress_normalize_input_interfaces_Some:
  assumes generic: "primitive_matcher_generic \<beta>"
      and "normalized_nnf_match m" and "compress_normalize_input_interfaces m = Some m'"
    shows "matches (\<beta>, \<alpha>) m' a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
    apply(rule compress_normalize_primitive_Some[OF assms(2) wf_disc_sel_common_primitive(5)])
     using assms(3) apply(simp add: compress_normalize_input_interfaces_def; fail)
    using compress_interfaces_Some[OF generic] by simp

  lemma compress_normalize_input_interfaces_None:
  assumes generic: "primitive_matcher_generic \<beta>"
      and "normalized_nnf_match m" and "compress_normalize_input_interfaces m = None"
    shows "\<not> matches (\<beta>, \<alpha>) m a p"
    apply(rule compress_normalize_primitive_None[OF assms(2) wf_disc_sel_common_primitive(5)])
     using assms(3) apply(simp add: compress_normalize_input_interfaces_def; fail)
    using compress_interfaces_None[OF generic] by simp

  lemma compress_normalize_input_interfaces_nnf: "normalized_nnf_match m \<Longrightarrow> compress_normalize_input_interfaces m = Some m' \<Longrightarrow>
      normalized_nnf_match m'"
    unfolding compress_normalize_input_interfaces_def
    using compress_normalize_primitive_nnf[OF wf_disc_sel_common_primitive(5)] by blast
 
  lemma compress_normalize_input_interfaces_not_introduces_Iiface:
    "\<not> has_disc is_Iiface m \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_input_interfaces m = Some m' \<Longrightarrow>
     \<not> has_disc is_Iiface m'"
      apply(simp add: compress_normalize_input_interfaces_def)
      apply(drule compress_normalize_primitive_not_introduces_C[where m=m and C'=IIface])
          apply(simp_all add: wf_disc_sel_common_primitive(5))
      by(simp add: compress_interfaces_def iface_is_wildcard_ifaceAny)
      
  lemma compress_normalize_input_interfaces_not_introduces_Iiface_negated:
    assumes notdisc: "\<not> has_disc_negated is_Iiface False m"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_input_interfaces m = Some m'"
     shows "\<not> has_disc_negated is_Iiface False m'"
     apply(rule compress_normalize_primitive_not_introduces_C_negated[OF notdisc wf_disc_sel_common_primitive(5) nm])
     using some apply(simp add: compress_normalize_input_interfaces_def)
     by(simp add: compress_interfaces_def split: option.split_asm if_split_asm)

  (* only for arbitrary discs that do not match Iiface*)
  lemma compress_normalize_input_interfaces_hasdisc:
    "\<not> has_disc disc m \<Longrightarrow> (\<forall>a. \<not> disc (IIface a)) \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_input_interfaces m = Some m' \<Longrightarrow>
     normalized_nnf_match m' \<and> \<not> has_disc disc m'"
     unfolding compress_normalize_input_interfaces_def
     using compress_normalize_primitive_hasdisc[OF _ wf_disc_sel_common_primitive(5)] by blast

   (* only for arbitrary discs that do not match Iiface*)
  lemma compress_normalize_input_interfaces_hasdisc_negated:
    "\<not> has_disc_negated disc neg m \<Longrightarrow> (\<forall>a. \<not> disc (IIface a)) \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_input_interfaces m = Some m' \<Longrightarrow>
     normalized_nnf_match m' \<and> \<not> has_disc_negated disc neg m'"
     unfolding compress_normalize_input_interfaces_def
     using compress_normalize_primitive_hasdisc_negated[OF _ wf_disc_sel_common_primitive(5)] by blast

  lemma compress_normalize_input_interfaces_preserves_normalized_n_primitive:
    "normalized_n_primitive (disc, sel) P m \<Longrightarrow> (\<forall>a. \<not> disc (IIface a)) \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_input_interfaces m = Some m' \<Longrightarrow>
     normalized_nnf_match m' \<and> normalized_n_primitive (disc, sel) P m'"
     unfolding compress_normalize_input_interfaces_def
   using compress_normalize_primitve_preserves_normalized_n_primitive[OF _ wf_disc_sel_common_primitive(5)] by blast
  



  value[code] "compress_normalize_input_interfaces 
    (MatchAnd (MatchAnd (MatchAnd (Match ((IIface (Iface ''eth+'')::32 common_primitive))) (MatchNot (Match (IIface (Iface ''eth4''))))) (Match (IIface (Iface ''eth1''))))
              (Match (Prot (Proto TCP))))"
    
  value[code] "compress_normalize_input_interfaces (MatchAny:: 32 common_primitive match_expr)"




  definition compress_normalize_output_interfaces :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr option" where 
    "compress_normalize_output_interfaces m \<equiv> compress_normalize_primitive (is_Oiface, oiface_sel) OIface compress_interfaces m"

  lemma compress_normalize_output_interfaces_Some:
  assumes generic: "primitive_matcher_generic \<beta>"
      and "normalized_nnf_match m" and "compress_normalize_output_interfaces m = Some m'"
    shows "matches (\<beta>, \<alpha>) m' a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
    apply(rule compress_normalize_primitive_Some[OF assms(2) wf_disc_sel_common_primitive(6)])
     using assms(3) apply(simp add: compress_normalize_output_interfaces_def; fail)
    using compress_interfaces_Some[OF generic] by simp

  lemma compress_normalize_output_interfaces_None:
  assumes generic: "primitive_matcher_generic \<beta>"
      and "normalized_nnf_match m" and "compress_normalize_output_interfaces m = None"
    shows "\<not> matches (\<beta>, \<alpha>) m a p"
    apply(rule compress_normalize_primitive_None[OF assms(2) wf_disc_sel_common_primitive(6)])
     using assms(3) apply(simp add: compress_normalize_output_interfaces_def; fail)
    using compress_interfaces_None[OF generic] by simp

  lemma compress_normalize_output_interfaces_nnf: "normalized_nnf_match m \<Longrightarrow> compress_normalize_output_interfaces m = Some m' \<Longrightarrow>
      normalized_nnf_match m'"
    unfolding compress_normalize_output_interfaces_def
    using compress_normalize_primitive_nnf[OF wf_disc_sel_common_primitive(6)] by blast
 
  lemma compress_normalize_output_interfaces_not_introduces_Oiface:
    "\<not> has_disc is_Oiface m \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_output_interfaces m = Some m' \<Longrightarrow>
     \<not> has_disc is_Oiface m'"
      apply(simp add: compress_normalize_output_interfaces_def)
      apply(drule compress_normalize_primitive_not_introduces_C[where m=m  and C'=OIface])
          apply(simp_all add: wf_disc_sel_common_primitive(6))
      by(simp add: compress_interfaces_def iface_is_wildcard_ifaceAny)
      
  lemma compress_normalize_output_interfaces_not_introduces_Oiface_negated:
    assumes notdisc: "\<not> has_disc_negated is_Oiface False m"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_output_interfaces m = Some m'"
     shows "\<not> has_disc_negated is_Oiface False m'"
     apply(rule compress_normalize_primitive_not_introduces_C_negated[OF notdisc wf_disc_sel_common_primitive(6) nm])
     using some apply(simp add: compress_normalize_output_interfaces_def)
     by(simp add: compress_interfaces_def split: option.split_asm if_split_asm)

  (* only for arbitrary discs that do not match Oiface*)
  lemma compress_normalize_output_interfaces_hasdisc:
    "\<not> has_disc disc m \<Longrightarrow> (\<forall>a. \<not> disc (OIface a)) \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_output_interfaces m = Some m' \<Longrightarrow>
     normalized_nnf_match m' \<and> \<not> has_disc disc m'"
     unfolding compress_normalize_output_interfaces_def
     using compress_normalize_primitive_hasdisc[OF _ wf_disc_sel_common_primitive(6)] by blast

   (* only for arbitrary discs that do not match Oiface*)
  lemma compress_normalize_output_interfaces_hasdisc_negated:
    "\<not> has_disc_negated disc neg m \<Longrightarrow> (\<forall>a. \<not> disc (OIface a)) \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_output_interfaces m = Some m' \<Longrightarrow>
     normalized_nnf_match m' \<and> \<not> has_disc_negated disc neg m'"
     unfolding compress_normalize_output_interfaces_def
     using compress_normalize_primitive_hasdisc_negated[OF _ wf_disc_sel_common_primitive(6)] by blast

  lemma compress_normalize_output_interfaces_preserves_normalized_n_primitive:
    "normalized_n_primitive (disc, sel) P m \<Longrightarrow> (\<forall>a. \<not> disc (OIface a)) \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_output_interfaces m = Some m' \<Longrightarrow>
     normalized_nnf_match m' \<and> normalized_n_primitive (disc, sel) P m'"
     unfolding compress_normalize_output_interfaces_def
   using compress_normalize_primitve_preserves_normalized_n_primitive[OF _ wf_disc_sel_common_primitive(6)] by blast

end

end
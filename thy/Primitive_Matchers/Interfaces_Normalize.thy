theory Interfaces_Normalize
imports Common_Primitive_Lemmas
begin


(*TODO move to separate file*)

fun compress_normalize_primitive_monad :: "('a match_expr \<Rightarrow> 'a match_expr option) list \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr option" where
  "compress_normalize_primitive_monad [] m = Some m" |
  "compress_normalize_primitive_monad (f#fs) m = (case f m of None \<Rightarrow> None
                                                           |  Some m' \<Rightarrow> compress_normalize_primitive_monad fs m')"

lemma compress_normalize_primitive_monad: 
      assumes "\<And>m m' f. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> matches \<gamma> m' a p \<longleftrightarrow> matches \<gamma> m a p"
          and "\<And>m m' f. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> normalized_nnf_match m'"
          and "normalized_nnf_match m"
          and "(compress_normalize_primitive_monad fs m) = Some m'"
      shows "matches \<gamma> m' a p \<longleftrightarrow> matches \<gamma> m a p" (is ?goal1)
        and "normalized_nnf_match m'"              (is ?goal2)
  proof -
    (*everything in one big induction*)
    have goals: "?goal1 \<and> ?goal2"
    using assms proof(induction fs arbitrary: m)
    case Nil thus ?case by simp
    next
    case (Cons f fs)
      from Cons.prems(1) have IH_prem1:
        "(\<And>f m m'. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> matches \<gamma> m' a p = matches \<gamma> m a p)" by auto
      from Cons.prems(2) have IH_prem2:
        "(\<And>f m m'. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> normalized_nnf_match m')" by auto
      from Cons.IH IH_prem1 IH_prem2 have
        IH: "\<And>m. normalized_nnf_match m \<Longrightarrow> compress_normalize_primitive_monad fs m = Some m' \<Longrightarrow>
                  (matches \<gamma> m' a p \<longleftrightarrow> matches \<gamma> m a p) \<and> ?goal2" by fast
      show ?case
        proof(cases "f m")
          case None thus ?thesis using Cons.prems by auto
        next
          case(Some m'')
            from Some Cons.prems(1)[of f] Cons.prems(3) have 1: "matches \<gamma> m'' a p = matches \<gamma> m a p" by simp
            from Some Cons.prems(2)[of f] Cons.prems(3) have 2: "normalized_nnf_match m''" by simp
            from Some have "compress_normalize_primitive_monad (f # fs) m = compress_normalize_primitive_monad fs m''" by simp
            thus ?thesis using Cons.prems(4) IH 1 2 by auto 
        qed
    qed
    from goals show ?goal1 by simp
    from goals show ?goal2 by simp
  qed

(*TODO: proof is a bit too much sledgehammered in parts*)
lemma compress_normalize_primitive_monad_None: 
      assumes "\<And>m m' f. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> matches \<gamma> m' a p \<longleftrightarrow> matches \<gamma> m a p"
          and "\<And>m f. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = None \<Longrightarrow> \<not> matches \<gamma> m a p"
          and "\<And>m m' f. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> normalized_nnf_match m'"
          and "normalized_nnf_match m"
          and "(compress_normalize_primitive_monad fs m) = None"
      shows "\<not> matches \<gamma> m a p"
    using assms proof(induction fs arbitrary: m)
    case Nil thus ?case by simp
    next
    case (Cons f fs)
      from Cons.prems(1) have IH_prem1:
        "(\<And>f m m'. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> matches \<gamma> m' a p = matches \<gamma> m a p)" by auto
      from Cons.prems(2) have IH_prem2:
        "(\<And>f m m'. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = None \<Longrightarrow> \<not> matches \<gamma> m a p)" by auto
      from Cons.prems(3) have IH_prem3:
        "(\<And>f m m'. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> normalized_nnf_match m')" by auto
      from Cons.IH IH_prem1 IH_prem2 IH_prem3 have
        IH: "\<And>m. normalized_nnf_match m \<Longrightarrow> compress_normalize_primitive_monad fs m = None \<Longrightarrow> \<not>  matches \<gamma> m a p" by blast
      show ?case
        proof(cases "f m")
          case None thus ?thesis using Cons.prems(4) Cons.prems(2) Cons.prems(3) by auto
        next
          case(Some m'')
            from Some Cons.prems(3)[of f] Cons.prems(4) have 2: "normalized_nnf_match m''" by simp
            from Some have "compress_normalize_primitive_monad (f # fs) m = compress_normalize_primitive_monad fs m''" by simp
            hence "\<not> matches \<gamma> m'' a p" using Cons.prems(5) IH 2 by simp
            thus ?thesis using Cons.prems(1) Cons.prems(4) Some by auto 
        qed
    qed


lemma compress_normalize_primitive_monad_preserves:
      assumes "\<And>m m' f. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> normalized_nnf_match m'"
          and "\<And>m m' f. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> P m \<Longrightarrow> f m = Some m' \<Longrightarrow> P m'"
          and "normalized_nnf_match m"
          and "P m"
          and "(compress_normalize_primitive_monad fs m) = Some m'"
      shows "normalized_nnf_match m' \<and> P m'"
    using assms proof(induction fs arbitrary: m)
    case Nil thus ?case by simp
    next
    case (Cons f fs) thus ?case by(simp split: option.split_asm) blast (*1s*)
    qed
    


subsection{*Optimizing interfaces in match expressions*}

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

  (*TODO: if positive iface is not a wildcard and whole expression is not none, then drop all negative interfaces from the expression*)


term map_option
term option_map (*l4v*)

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
       apply(simp split:split_if_asm)
       using iface_subset apply blast
       apply(drule_tac p_i="p_oiface p" in compress_pos_interfaces_None)
       apply(simp; fail)
      apply(drule_tac p_i="p_oiface p" in compress_pos_interfaces_Some)
      apply(simp split:split_if_asm)
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
       apply(simp split:split_if_asm)
         using iface_is_wildcard_def iface_subset match_iface_case_nowildcard apply fastforce
        using match_ifaceAny apply blast
       apply force
      apply(drule_tac p_i="p_oiface p" in compress_pos_interfaces_Some)
      apply(simp split:split_if_asm)
        using iface_is_wildcard_def iface_subset match_iface_case_nowildcard apply fastforce
       using match_ifaceAny apply blast
      by force

  
  definition compress_normalize_input_interfaces :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr option" where 
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
      apply(drule compress_normalize_primitive_not_introduces_C[where m=m])
          apply(simp_all add: wf_disc_sel_common_primitive(5))
      by(simp add: compress_interfaces_def iface_is_wildcard_ifaceAny)
      
  lemma compress_normalize_input_interfaces_not_introduces_Iiface_negated:
    assumes notdisc: "\<not> has_disc_negated is_Iiface False m"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_input_interfaces m = Some m'"
     shows "\<not> has_disc_negated is_Iiface False m'"
     apply(rule compress_normalize_primitive_not_introduces_C_negated[OF notdisc wf_disc_sel_common_primitive(5) nm])
     using some apply(simp add: compress_normalize_input_interfaces_def)
     by(simp add: compress_interfaces_def split: option.split_asm split_if_asm)

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
    (MatchAnd (MatchAnd (MatchAnd (Match (IIface (Iface ''eth+''))) (MatchNot (Match (IIface (Iface ''eth4''))))) (Match (IIface (Iface ''eth1''))))
              (Match (Prot (Proto TCP))))"
    
  value[code] "compress_normalize_input_interfaces MatchAny"




  definition compress_normalize_output_interfaces :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr option" where 
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
      apply(drule compress_normalize_primitive_not_introduces_C[where m=m])
          apply(simp_all add: wf_disc_sel_common_primitive(6))
      by(simp add: compress_interfaces_def iface_is_wildcard_ifaceAny)
      
  lemma compress_normalize_output_interfaces_not_introduces_Oiface_negated:
    assumes notdisc: "\<not> has_disc_negated is_Oiface False m"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_output_interfaces m = Some m'"
     shows "\<not> has_disc_negated is_Oiface False m'"
     apply(rule compress_normalize_primitive_not_introduces_C_negated[OF notdisc wf_disc_sel_common_primitive(6) nm])
     using some apply(simp add: compress_normalize_output_interfaces_def)
     by(simp add: compress_interfaces_def split: option.split_asm split_if_asm)

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
theory Protocols_Normalize
imports Common_Primitive_Lemmas
  "../Bitmagic/Word_Upto"
begin


subsection\<open>Optimizing protocols in match expressions\<close>


  fun compress_pos_protocols :: "protocol list \<Rightarrow> protocol option" where
    "compress_pos_protocols [] = Some ProtoAny" |
    "compress_pos_protocols [p] = Some p" |
    "compress_pos_protocols (p1#p2#ps) = (case simple_proto_conjunct p1 p2 of None \<Rightarrow> None | Some p \<Rightarrow> compress_pos_protocols (p#ps))"

  lemma compress_pos_protocols_Some: "compress_pos_protocols ps = Some proto \<Longrightarrow> 
          match_proto proto p_prot \<longleftrightarrow> (\<forall> p \<in> set ps. match_proto p p_prot)"
    apply(induction ps rule: compress_pos_protocols.induct)
      apply (simp; fail)
     apply(simp; fail)
    apply(simp)
    apply(rename_tac p1 p2 pps)
    apply(case_tac "simple_proto_conjunct p1 p2")
     apply(simp; fail)
    apply(simp)
    using simple_proto_conjunct_Some by presburger

  lemma compress_pos_protocols_None: "compress_pos_protocols ps = None \<Longrightarrow> 
          \<not> (\<forall> proto \<in> set ps. match_proto proto p_prot)"
    apply(induction ps rule: compress_pos_protocols.induct)
      apply (simp; fail)
     apply(simp; fail)
    apply(simp)
    apply(rename_tac i1 i2 iis)
    apply(case_tac "simple_proto_conjunct i1 i2")
     apply(simp_all)
     using simple_proto_conjunct_None apply blast
    using simple_proto_conjunct_Some by blast

(*TODO move and give a name?*)
(*the intuition behind the compress_protocols*)
lemma "simple_proto_conjunct (Proto p1) (Proto p2) \<noteq> None \<Longrightarrow> \<forall>pkt. match_proto (Proto p1) pkt \<longleftrightarrow> match_proto (Proto p2) pkt"
  apply(subgoal_tac "p1 = p2")
   apply(simp)
  apply(simp split: split_if_asm)
  done
lemma "simple_proto_conjunct p1 (Proto p2) \<noteq> None \<Longrightarrow> \<forall>pkt. match_proto (Proto p2) pkt \<longrightarrow> match_proto p1 pkt"
 apply(cases p1)
  apply(simp)
 apply(simp split: split_if_asm)
 done

  (*TODO: optimize more? maybe?*)
  definition compress_protocols :: "protocol negation_type list \<Rightarrow> (protocol list \<times> protocol list) option" where
    "compress_protocols ps \<equiv> case (compress_pos_protocols (getPos ps))
        of None \<Rightarrow> None
        |  Some proto \<Rightarrow> if ProtoAny \<in> set (getNeg ps) \<or> (\<forall>p \<in> {0..max_word}. Proto p \<in> set (getNeg ps)) then
                           None
                         else if proto = ProtoAny then
                           Some ([], getNeg ps)
                         else if (\<exists>p \<in> set (getNeg ps). simple_proto_conjunct proto p \<noteq> None) then
                           None
                         else
                           Some ([proto], getNeg ps)"
  
  (* It is kind of messy to find a definition that checks whether a match is the exhaustive list and is executable *)
  (*TODO: probably code_unfold was meant. TODO: check whether we actually need this!*)
  (*Changed to code_unfold. TODO: move and check if this breaks anything*)
  (*TODO: no longer code_unfold, needs testing!*)
  lemma all_proto_hlp2: "ProtoAny \<in> a \<or> (\<forall>p \<in> {0..max_word}. Proto p \<in> a) \<longleftrightarrow>
                               ProtoAny \<in> a \<or> a = {p. p \<noteq> ProtoAny}"
  proof -   
    have all_proto_hlp: "ProtoAny \<notin> a \<Longrightarrow> (\<forall>p \<in> {0..max_word}. Proto p \<in> a) \<longleftrightarrow> a = {p. p \<noteq> ProtoAny}"
      by(auto intro: protocol.exhaust)
    thus ?thesis by blast
  qed

  lemma set_word8_word_upto: "{0..(max_word :: 8 word)} = set (word_upto 0 255)"
    apply(simp add: max_word_def)
    apply(safe)
     apply(simp add: word_upto_set_eq)
    apply(simp add: word_upto_set_eq)
    done
  lemma "(\<forall>p \<in> {0..max_word}. Proto p \<in> set (getNeg ps)) \<longleftrightarrow>
         ((\<forall>p \<in> set (word_upto 0 255). Proto p \<in> set (getNeg ps)))"
    by(simp add: set_word8_word_upto)
  (*
        "../afp/Mergesort" (*TODO: dependnecy! import from afp directly!*)
  lemma "of_int ` {0..255} = {0:: 8 word..255}"
    oops
  lemma "(\<forall>p \<in> {0..max_word}. Proto p \<in> set (getNeg ps)) \<longleftrightarrow>
         (mergesort_remdups (List.map_filter (\<lambda>p. case p of Proto x \<Rightarrow> Some x | ProtoAny \<Rightarrow> None) (getNeg ps)) =
          word_upto 0 255)"
    apply(rule iffI)
    subgoal
     apply(rule List.linorder_class.sorted_distinct_set_unique)
     apply(simp_all add: Mergesort.mergesort_remdups_correct)
     prefer 3
    oops
  *)
  
  lemma compress_protocols_code[code]: (*does not seem better*)
    "compress_protocols ps = (case (compress_pos_protocols (getPos ps))
        of None \<Rightarrow> None
        |  Some proto \<Rightarrow> if ProtoAny \<in> set (getNeg ps) \<or> (\<forall>p \<in> set (word_upto 0 255). Proto p \<in> set (getNeg ps)) then
                           None
                         else if proto = ProtoAny then
                           Some ([], getNeg ps)
                         else if (\<exists>p \<in> set (getNeg ps). simple_proto_conjunct proto p \<noteq> None) then
                           None
                         else
                           Some ([proto], getNeg ps)
        )"
    unfolding compress_protocols_def
    using set_word8_word_upto by presburger

  (*fully optimized, i.e. we cannot compress it better*)
  lemma "compress_protocols ps = Some (ps_pos, ps_neg) \<Longrightarrow>
    \<exists> p. ((\<forall>m\<in>set ps_pos. match_proto m p) \<and> (\<forall>m\<in>set ps_neg. \<not> match_proto m p))"
    apply(simp add: compress_protocols_def all_proto_hlp2 split: option.split_asm split_if_asm)
     defer
     apply(clarify)
     apply(rename_tac p)
     apply(case_tac p, simp_all)
     apply(rename_tac p_primitive)
     using simple_proto_conjunct_None apply auto[1]
    apply(subgoal_tac "\<exists>p. (Proto p) \<notin> set ps_neg")
     apply(elim exE)
     apply(rename_tac x2 p)
     apply(rule_tac x=p in exI)
     apply(blast elim: match_proto.elims)
    apply(auto intro: protocol.exhaust)
    done
  
  definition compress_normalize_protocols :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr option" where 
    "compress_normalize_protocols m \<equiv> compress_normalize_primitive (is_Prot, prot_sel) Prot compress_protocols m"

  lemma (in primitive_matcher_generic) compress_normalize_protocols_Some:
  assumes "normalized_nnf_match m" and "compress_normalize_protocols m = Some m'"
    shows "matches (\<beta>, \<alpha>) m' a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
  proof(rule compress_normalize_primitive_Some[OF assms(1) wf_disc_sel_common_primitive(7), of compress_protocols])
    show "compress_normalize_primitive (is_Prot, prot_sel) Prot compress_protocols m = Some m'"
      using assms(2) by(simp add: compress_normalize_protocols_def)
  next
    fix ps ps_pos ps_neg
    show "compress_protocols ps = Some (ps_pos, ps_neg) \<Longrightarrow>
      matches (\<beta>, \<alpha>) (alist_and (NegPos_map Prot ((map Pos ps_pos)@(map Neg ps_neg)))) a p \<longleftrightarrow>
      matches (\<beta>, \<alpha>) (alist_and (NegPos_map Prot ps)) a p"
      apply(simp add: compress_protocols_def)
      apply(simp add: bunch_of_lemmata_about_matches alist_and_append NegPos_map_append)
      apply(simp add: nt_match_list_matches[symmetric] nt_match_list_simp)
      apply(simp add: NegPos_map_simps Prot_single Prot_single_not)
      apply(case_tac "compress_pos_protocols (getPos ps)")
       apply(simp_all)
      apply(drule_tac p_prot="p_proto p" in compress_pos_protocols_Some)
      apply(simp split:split_if_asm)
      by force
  qed

  lemma (in primitive_matcher_generic) compress_normalize_protocols_None:
  assumes "normalized_nnf_match m" and "compress_normalize_protocols m = None"
    shows "\<not> matches (\<beta>, \<alpha>) m a p"
  proof(rule compress_normalize_primitive_None[OF assms(1) wf_disc_sel_common_primitive(7), of "compress_protocols"])
    show "compress_normalize_primitive (is_Prot, prot_sel) Prot compress_protocols m = None"  
      using assms(2) by(simp add: compress_normalize_protocols_def)
    next
      fix ps
      have if_option_Some:
        "((if P then None else Some x) = Some y) = (\<not>P \<and> x = y)"
        for P and x::protocol and y by simp
      show "compress_protocols ps = None \<Longrightarrow> \<not> matches (\<beta>, \<alpha>) (alist_and (NegPos_map Prot ps)) a p"
        apply(simp add: compress_protocols_def)
        apply(simp add: nt_match_list_matches[symmetric] nt_match_list_simp)
        apply(simp add: NegPos_map_simps Prot_single Prot_single_not)
        apply(cases "compress_pos_protocols (getPos ps)")
         apply(simp_all)
         apply(drule_tac p_prot="p_proto p" in compress_pos_protocols_None)
         apply(simp; fail)
        apply(drule_tac p_prot="p_proto p" in compress_pos_protocols_Some)
        apply(simp split:split_if_asm)
         apply fastforce
        apply(elim bexE exE)
        apply(simp)
        (*by (metis (full_types) option.distinct(1) simple_proto_conjunct.elims)*)
        apply(elim simple_proto_conjunct.elims)
          apply(simp; fail)
         apply(simp; fail)
        using if_option_Some by metis
    qed

  lemma compress_normalize_protocols_nnf: "normalized_nnf_match m \<Longrightarrow> compress_normalize_protocols m = Some m' \<Longrightarrow>
      normalized_nnf_match m'"
    unfolding compress_normalize_protocols_def
    using compress_normalize_primitive_nnf[OF wf_disc_sel_common_primitive(7)] by blast
 
  lemma compress_normalize_protocols_not_introduces_Prot:
    "\<not> has_disc is_Prot m \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_protocols m = Some m' \<Longrightarrow>
     \<not> has_disc is_Prot m'"
      apply(simp add: compress_normalize_protocols_def)
      apply(drule compress_normalize_primitive_not_introduces_C[where m=m])
          apply(simp_all add: wf_disc_sel_common_primitive(7))
      apply(simp add: compress_protocols_def split: if_splits)
      done

  lemma compress_normalize_protocols_not_introduces_Prot_negated:
    assumes notdisc: "\<not> has_disc_negated is_Prot False m"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_protocols m = Some m'"
     shows "\<not> has_disc_negated is_Prot False m'"
     apply(rule compress_normalize_primitive_not_introduces_C_negated[OF notdisc wf_disc_sel_common_primitive(7) nm])
     using some apply(simp add: compress_normalize_protocols_def)
     by(simp add: compress_protocols_def split: option.split_asm split_if_asm)


  lemma compress_normalize_protocols_hasdisc:
    "\<not> has_disc disc m \<Longrightarrow> (\<forall>a. \<not> disc (Prot a)) \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_protocols m = Some m' \<Longrightarrow>
     normalized_nnf_match m' \<and> \<not> has_disc disc m'"
     unfolding compress_normalize_protocols_def
     using compress_normalize_primitive_hasdisc[OF _ wf_disc_sel_common_primitive(7)] by blast

  lemma compress_normalize_protocols_hasdisc_negated:
    "\<not> has_disc_negated disc neg m \<Longrightarrow> (\<forall>a. \<not> disc (Prot a)) \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_protocols m = Some m' \<Longrightarrow>
     normalized_nnf_match m' \<and> \<not> has_disc_negated disc neg m'"
     unfolding compress_normalize_protocols_def
     using compress_normalize_primitive_hasdisc_negated[OF _ wf_disc_sel_common_primitive(7)] by blast


  lemma compress_normalize_protocols_preserves_normalized_n_primitive:
    "normalized_n_primitive (disc, sel) P m \<Longrightarrow> (\<forall>a. \<not> disc (Prot a)) \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_protocols m = Some m' \<Longrightarrow>
     normalized_nnf_match m' \<and> normalized_n_primitive (disc, sel) P m'"
     unfolding compress_normalize_protocols_def
   using compress_normalize_primitve_preserves_normalized_n_primitive[OF _ wf_disc_sel_common_primitive(7)] by blast
  

  (*TODO: optimize much much much more!*)
  value[code] "compress_normalize_protocols 
    (MatchAnd (MatchAnd (MatchAnd (Match ((Prot (Proto TCP)):: 32 common_primitive)) (MatchNot (Match (Prot (Proto UDP))))) (Match (IIface (Iface ''eth1''))))
              (Match (Prot (Proto TCP))))"
    
  value[code] "compress_normalize_protocols (MatchAny:: 32 common_primitive match_expr)"


  

end

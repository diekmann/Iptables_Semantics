theory Protocols_Normalize
imports Common_Primitive_Lemmas
  "../Common/Word_Upto"
  Ports_Normalize (*TODO: remove dependency*)
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
                           Some ([proto], [])"
  
  (* It is kind of messy to find a definition that checks whether a match is the exhaustive list
    and is executable *)
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
 
  
  lemma compress_protocols_code[code]:
    "compress_protocols ps = (case (compress_pos_protocols (getPos ps))
        of None \<Rightarrow> None
        |  Some proto \<Rightarrow> if ProtoAny \<in> set (getNeg ps) \<or> (\<forall>p \<in> set (word_upto 0 255). Proto p \<in> set (getNeg ps)) then
                           None
                         else if proto = ProtoAny then
                           Some ([], getNeg ps)
                         else if (\<exists>p \<in> set (getNeg ps). simple_proto_conjunct proto p \<noteq> None) then
                           None
                         else
                          (*proto is a primitive_protocol here. This is  strict equality match, e.g.
                            protocol must be TCP. Thus, we can remove all negative matches!*)
                           Some ([proto], [])
        )"
    unfolding compress_protocols_def
    using set_word8_word_upto by presburger

  (*fully optimized, i.e. we cannot compress it better*)
  lemma "compress_protocols ps = Some (ps_pos, ps_neg) \<Longrightarrow>
    \<exists> p. ((\<forall>m\<in>set ps_pos. match_proto m p) \<and> (\<forall>m\<in>set ps_neg. \<not> match_proto m p))"
    apply(simp add: compress_protocols_def all_proto_hlp2 split: option.split_asm split_if_asm)
     defer
     apply(clarify)
     subgoal for p
     apply(case_tac p, simp)
     apply(rename_tac p_primitive)
     using simple_proto_conjunct_None by auto[1]
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
      using simple_proto_conjunct_None by auto
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
        apply(elim simple_proto_conjunct.elims)
          apply(simp; fail)
         apply(simp; fail)
        using if_option_Some by metis
    qed

  lemma compress_normalize_protocols_nnf:
    "normalized_nnf_match m \<Longrightarrow> compress_normalize_protocols m = Some m' \<Longrightarrow>
      normalized_nnf_match m'"
    unfolding compress_normalize_protocols_def
    using compress_normalize_primitive_nnf[OF wf_disc_sel_common_primitive(7)] by blast
 
  (*TODO: not needed, I probably want it to introduce prot!*)
  lemma compress_normalize_protocols_not_introduces_Prot:
    "\<not> has_disc is_Prot m \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> compress_normalize_protocols m = Some m' \<Longrightarrow>
     \<not> has_disc is_Prot m'"
      apply(simp add: compress_normalize_protocols_def)
      apply(drule compress_normalize_primitive_not_introduces_C[where m=m and C'=Prot])
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
  

  (*TODO: add protocols from positive L4 ports into optimization*)

  lemma "case compress_normalize_protocols 
    (MatchAnd (MatchAnd (MatchAnd (Match ((Prot (Proto TCP)):: 32 common_primitive)) (MatchNot (Match (Prot (Proto UDP))))) (Match (IIface (Iface ''eth1''))))
              (Match (Prot (Proto TCP)))) of Some ps \<Rightarrow> opt_MatchAny_match_expr ps
  = MatchAnd (Match (Prot (Proto 6))) (MatchAnd MatchAny (Match (IIface (Iface ''eth1''))))" by eval
    
  value[code] "compress_normalize_protocols (MatchAny:: 32 common_primitive match_expr)"


  definition import_protocols_from_ports
    :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr" where 
  "import_protocols_from_ports m \<equiv>
    (case primitive_extractor (is_Src_Ports, src_ports_sel) m of (srcpts, rst1) \<Rightarrow>
     case primitive_extractor (is_Dst_Ports, dst_ports_sel) rst1 of (dstpts, rst2) \<Rightarrow>
      MatchAnd
      (MatchAnd
       (MatchAnd
        (andfold_MatchExp (map (Match \<circ> (Prot \<circ> (case_ipt_l4_ports (\<lambda>proto x. Proto proto)))) (getPos srcpts)))
        (andfold_MatchExp (map (Match \<circ> (Prot \<circ> (case_ipt_l4_ports (\<lambda>proto x. Proto proto)))) (getPos dstpts)))
       )
        (alist_and' (NegPos_map Src_Ports srcpts @ NegPos_map Dst_Ports dstpts))
       )
         rst2
     )"

  value "import_protocols_from_ports 
    (MatchAnd (MatchAnd (MatchAnd (Match ((Prot (Proto TCP)):: 32 common_primitive))
      (Match (Src_Ports (L4Ports UDP [])))) (Match (IIface (Iface ''eth1''))))
              (Match (Prot (Proto TCP))))"


  (*unfolding the whole primitive_extractor*)
  lemma import_protocols_from_ports_erule: "normalized_nnf_match m \<Longrightarrow> P m \<Longrightarrow>
    (\<And>srcpts rst1 dstpts rst2.
       normalized_nnf_match m \<Longrightarrow>
       (*P m \<Longrightarrow> erule consumes only first argument*)
       primitive_extractor (is_Src_Ports, src_ports_sel) m = (srcpts, rst1) \<Longrightarrow>
       primitive_extractor (is_Dst_Ports, dst_ports_sel) rst1 = (dstpts, rst2) \<Longrightarrow>
       normalized_nnf_match rst1 \<Longrightarrow>
       normalized_nnf_match rst2 \<Longrightarrow>
       P (MatchAnd
           (MatchAnd
             (MatchAnd
               (andfold_MatchExp
                 (map (Match \<circ> (Prot \<circ> (case_ipt_l4_ports (\<lambda>proto x. Proto proto)))) (getPos srcpts)))
               (andfold_MatchExp
                 (map (Match \<circ> (Prot \<circ> (case_ipt_l4_ports (\<lambda>proto x. Proto proto)))) (getPos dstpts))))
             (alist_and' (NegPos_map Src_Ports srcpts @ NegPos_map Dst_Ports dstpts)))
           rst2)) \<Longrightarrow>
    P (import_protocols_from_ports m)"
    apply(simp add: import_protocols_from_ports_def)
    apply(case_tac "primitive_extractor (is_Src_Ports, src_ports_sel) m", rename_tac srcpts rst1)
    apply(simp)
    apply(case_tac "primitive_extractor (is_Dst_Ports, dst_ports_sel) rst1", rename_tac dstpts rst2)
    apply(simp)
    apply(frule(1) primitive_extractor_correct(2)[OF _ wf_disc_sel_common_primitive(1)])
    apply(frule(1) primitive_extractor_correct(2)[OF _ wf_disc_sel_common_primitive(2)])
    apply simp
    done

  lemma (in primitive_matcher_generic) import_protocols_from_ports:
  assumes normalized: "normalized_nnf_match m"
  shows "matches (\<beta>, \<alpha>) (import_protocols_from_ports m) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
  proof-
    have add_protocol:
    "matches (\<beta>, \<alpha>)
      (andfold_MatchExp (map (Match \<circ> (Prot \<circ> (case_ipt_l4_ports (\<lambda>proto x. Proto proto)))) (getPos as))) a p \<and>
     matches (\<beta>, \<alpha>) (alist_and (NegPos_map C as)) a p
     \<longleftrightarrow>
     matches (\<beta>, \<alpha>) (alist_and (NegPos_map C as)) a p"
    if C: "C = Src_Ports \<or> C = Dst_Ports" for C as
      proof(induction as)
      case Nil thus ?case by(simp)
      next
      case (Cons x xs)
        show ?case
        proof(cases x)
        case Neg with Cons.IH show ?thesis
          apply(simp add: bunch_of_lemmata_about_matches)
          by blast
        next
        case (Pos portmatch)
          with Cons.IH show ?thesis
            apply(cases portmatch)
            apply(simp add: andfold_MatchExp_matches bunch_of_lemmata_about_matches)
            using Ports_single_rewrite_Prot C by blast
        qed
      qed
  from normalized show ?thesis
    apply -
    apply(erule import_protocols_from_ports_erule)
     apply(simp; fail)
    apply(subst primitive_extractor_correct(1)[OF normalized wf_disc_sel_common_primitive(1),
          where \<gamma>="(\<beta>,\<alpha>)" and a=a and p=p, symmetric])
     apply(simp; fail)
    apply(drule(1) primitive_extractor_correct(1)[OF _ wf_disc_sel_common_primitive(2),
          where \<gamma>="(\<beta>,\<alpha>)" and a=a and p=p])
    apply(simp add: bunch_of_lemmata_about_matches matches_alist_and_alist_and' alist_and_append)
    using add_protocol by blast
  qed


  lemma import_protocols_from_ports_nnf:
    "normalized_nnf_match m \<Longrightarrow> normalized_nnf_match (import_protocols_from_ports m)"
    proof -
      have hlp: "\<forall>m\<in>set (map (Match \<circ> (Prot \<circ> (case_ipt_l4_ports (\<lambda>proto x. Proto proto)))) ls).
          normalized_nnf_match m" for ls
      apply(induction ls)
       apply(simp)
      apply(rename_tac l ls, case_tac l)
      by(simp)
    show "normalized_nnf_match m \<Longrightarrow> normalized_nnf_match (import_protocols_from_ports m)"
      apply(rule import_protocols_from_ports_erule)
        apply(simp_all)
      apply(simp add: normalized_nnf_match_alist_and')
      apply(safe)
       apply(rule andfold_MatchExp_normalized_nnf, simp add: hlp)+
      done
    qed

  lemma import_protocols_from_ports_not_introduces_Prot_negated:
    "normalized_nnf_match m \<Longrightarrow> \<not> has_disc_negated is_Prot False m \<Longrightarrow>
      \<not> has_disc_negated is_Prot False (import_protocols_from_ports m)"
     apply(erule(1) import_protocols_from_ports_erule)
     apply(simp)
     apply(intro conjI)
        using andfold_MatchExp_not_disc_negated_mapMatch[
          where C="Prot \<circ> case_ipt_l4_ports (\<lambda>proto x. Proto proto)", simplified] apply blast
       using andfold_MatchExp_not_disc_negated_mapMatch[
         where C="Prot \<circ> case_ipt_l4_ports (\<lambda>proto x. Proto proto)", simplified] apply blast
      apply(simp add: has_disc_negated_alist_and')
      using not_has_disc_negated_NegPos_map[where disc=is_Prot and C=Src_Ports, simplified]
            not_has_disc_negated_NegPos_map[where disc=is_Prot and C=Dst_Ports, simplified] apply blast
     apply(drule(1) primitive_extractor_correct(6)[OF _ wf_disc_sel_common_primitive(1), where neg=False])
     apply(drule(1) primitive_extractor_correct(6)[OF _ wf_disc_sel_common_primitive(2), where neg=False])
     by blast

end

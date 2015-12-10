theory Protocols_Normalize
imports Common_Primitive_Lemmas
begin


subsection{*Optimizing protocols in match expressions*}


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
        |  Some proto \<Rightarrow> if ProtoAny \<in> set (getNeg ps) then
                           None
                         else if proto = ProtoAny then
                           Some ([], getNeg ps)
                         else if (\<exists>p \<in> set (getNeg ps). simple_proto_conjunct proto p \<noteq> None) then
                           None
                         else
                           Some ([proto], getNeg ps)"


  lemma compress_protocols_None: "compress_protocols ps = None \<Longrightarrow> \<not> matches (common_matcher, \<alpha>) (alist_and (NegPos_map Prot ps)) a p"
    apply(simp add: compress_protocols_def)
    apply(simp add: nt_match_list_matches[symmetric] nt_match_list_simp)
    apply(simp add: NegPos_map_simps match_simplematcher_Prot match_simplematcher_Prot_not)
    apply(case_tac "compress_pos_protocols (getPos ps)")
     apply(simp_all)
     apply(drule_tac p_prot="p_proto p" in compress_pos_protocols_None)
     apply(simp; fail)
    apply(drule_tac p_prot="p_proto p" in compress_pos_protocols_Some)
    apply(simp split:split_if_asm)
     apply fastforce
    apply(elim bexE)
    by (metis if_option_Some simple_proto_conjunct.elims)



  lemma compress_protocol_Some: "compress_protocols ps = Some (ps_pos, ps_neg) \<Longrightarrow>
    matches (common_matcher, \<alpha>) (alist_and (NegPos_map Prot ((map Pos ps_pos)@(map Neg ps_neg)))) a p \<longleftrightarrow>
    matches (common_matcher, \<alpha>) (alist_and (NegPos_map Prot ps)) a p"
    apply(simp add: compress_protocols_def)
    apply(simp add: bunch_of_lemmata_about_matches(1) alist_and_append NegPos_map_append)
    apply(simp add: nt_match_list_matches[symmetric] nt_match_list_simp)
    apply(simp add: NegPos_map_simps match_simplematcher_Prot match_simplematcher_Prot_not)
    apply(case_tac "compress_pos_protocols (getPos ps)")
     apply(simp_all)
    apply(drule_tac p_prot="p_proto p" in compress_pos_protocols_Some)
    apply(simp split:split_if_asm)
    by force

  lemma primitive_protocol_Ex_neq: "p = Proto pi \<Longrightarrow> \<exists>p'. p' \<noteq> pi"
    by(cases pi) blast+
  lemma protocol_Ex_neq: "\<exists>p'. Proto p' \<noteq> p"
    by(cases p) (simp_all add: primitive_protocol_Ex_neq)
  lemma primitive_protocol_Ex_notin_list: "(\<exists>p. (Proto p) \<notin> set ps)"
    proof(cases "map (\<lambda>p. case p of Proto (OtherProtocol n) \<Rightarrow> n) (filter (\<lambda>p. case p of Proto (OtherProtocol _) \<Rightarrow> True | _ \<Rightarrow> False) ps)")
    case Nil 
      -- "arbitrary protocol number"
      hence "Proto (OtherProtocol 42) \<notin> set ps"
       apply(induction ps)
        apply(simp; fail)
       apply(simp split: protocol.split_asm split_if_asm primitive_protocol.split_asm; fail)
       done
      thus "\<exists>p. Proto p \<notin> set ps" by blast
    next
    case(Cons a as)
      have "\<exists>n::nat. n \<notin> set (a#as)" by (metis (full_types) lessI list.distinct(2) member_le_listsum_nat upt_conv_Nil upt_eq_list_intros(2))
      from this obtain n where "n \<notin> set (a#as)" by blast
      with Cons have "Proto (OtherProtocol n) \<notin> set ps"
        apply(induction ps)
         apply(simp; fail)
        apply(simp split: protocol.split_asm split_if_asm primitive_protocol.split_asm)
        by force
      thus "\<exists>p. Proto p \<notin> set ps" by blast
    qed

 

  (*fully optimized*)
  lemma "compress_protocols ps = Some (ps_pos, ps_neg) \<Longrightarrow>
    \<exists> p. ((\<forall>m\<in>set ps_pos. match_proto m p) \<and> (\<forall>m\<in>set ps_neg. \<not> match_proto m p))"
    apply(simp add: compress_protocols_def split: option.split_asm split_if_asm)
     defer
     apply(clarify)
     apply(rename_tac p)
     apply(case_tac p, simp_all)
     apply(rename_tac p_primitive)
     using simple_proto_conjunct_None apply auto[1]
    apply(induction ps_neg)
     apply(simp; fail)
    apply(simp, rename_tac psneg1 ps_neg aaa)
    apply(subgoal_tac "\<exists>p. (Proto p) \<notin> set (psneg1#ps_neg)")
     apply (metis list.set_intros(1) list.set_intros(2) match_proto.elims(2))
    using primitive_protocol_Ex_notin_list by presburger
  
  definition compress_normalize_protocols :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr option" where 
    "compress_normalize_protocols m \<equiv> compress_normalize_primitive (is_Prot, prot_sel) Prot compress_protocols m"

  lemma compress_normalize_protocols_Some:
  assumes "normalized_nnf_match m" and "compress_normalize_protocols m = Some m'"
    shows "matches (common_matcher, \<alpha>) m' a p \<longleftrightarrow> matches (common_matcher, \<alpha>) m a p"
    apply(rule compress_normalize_primitive_Some[OF assms(1) wf_disc_sel_common_primitive(7)])
     using assms(2) apply(simp add: compress_normalize_protocols_def; fail)
    using compress_protocol_Some by simp

  lemma compress_normalize_protocols_None:
  assumes "normalized_nnf_match m" and "compress_normalize_protocols m = None"
    shows "\<not> matches (common_matcher, \<alpha>) m a p"
    apply(rule compress_normalize_primitive_None[OF assms(1) wf_disc_sel_common_primitive(7)])
     using assms(2) apply(simp add: compress_normalize_protocols_def; fail)
    using compress_protocols_None by simp

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
      by(simp add: compress_protocols_def)

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
    (MatchAnd (MatchAnd (MatchAnd (Match (Prot (Proto TCP))) (MatchNot (Match (Prot (Proto UDP))))) (Match (IIface (Iface ''eth1''))))
              (Match (Prot (Proto TCP))))"
    
  value[code] "compress_normalize_protocols MatchAny"


  

end
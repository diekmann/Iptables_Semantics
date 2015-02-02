theory SimpleFw_Compliance
imports SimpleFw_Semantics "../Primitive_Matchers/IPPortIfaceSpace_Matcher" "../Semantics_Ternary"
        "../Output_Format/Negation_Type_Matching" "../Bitmagic/Numberwang_Ln"
begin

fun ipv4_word_netmask_to_ipt_ipv4range :: "(ipv4addr \<times> nat) \<Rightarrow> ipt_ipv4range" where
  "ipv4_word_netmask_to_ipt_ipv4range (ip, n) = Ip4AddrNetmask (dotteddecimal_of_ipv4addr ip) n"

fun ipt_ipv4range_to_ipv4_word_netmask :: " ipt_ipv4range \<Rightarrow> (ipv4addr \<times> nat)" where
  "ipt_ipv4range_to_ipv4_word_netmask (Ip4Addr ip_ddecim) = (ipv4addr_of_dotteddecimal ip_ddecim, 32)" | 
  "ipt_ipv4range_to_ipv4_word_netmask (Ip4AddrNetmask ip_ddecim n) = (ipv4addr_of_dotteddecimal ip_ddecim, n)"


(*do I need monads?*)
(*TODO: move*)
fun negation_type_to_match_expr :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a negation_type \<Rightarrow> 'b match_expr" where
  "negation_type_to_match_expr f (Pos a) = Match (f a)" |
  "negation_type_to_match_expr f (Neg a) = MatchNot (Match (f a))"


subsection{*Simple Match to MatchExpr*}

fun simple_match_to_ipportiface_match :: "simple_match \<Rightarrow> ipportiface_rule_match match_expr" where
  "simple_match_to_ipportiface_match \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr> = 
    MatchAnd (Match (IIface iif)) (MatchAnd (Match (OIface oif)) 
    (MatchAnd (Match (Src (ipv4_word_netmask_to_ipt_ipv4range sip)) )
    (MatchAnd (Match (Dst (ipv4_word_netmask_to_ipt_ipv4range dip)) )
    (MatchAnd (Match (Prot p))
    (MatchAnd (Match (Src_Ports [sps]))
    (Match (Dst_Ports [dps]))
    )))))"



(*is this usefull?*)
lemma xxx: "matches \<gamma> (simple_match_to_ipportiface_match \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr>) a p \<longleftrightarrow> 
      matches \<gamma> (alist_and ([Pos (IIface iif), Pos (OIface oif)] @ [Pos (Src (ipv4_word_netmask_to_ipt_ipv4range sip))]
        @ [Pos (Dst (ipv4_word_netmask_to_ipt_ipv4range dip))] @ [Pos (Prot p)]
        @ [Pos (Src_Ports [sps])] @ [Pos (Dst_Ports [dps])])) a p"
apply(simp add:)
apply(cases sip)
apply(simp_all)
apply(case_tac [!] dip)
apply(simp_all)
apply(simp_all add: bunch_of_lemmata_about_matches)
done

(*TODO: smelly duplication*)
lemma matches_SrcDst_simple_match: "p_src p \<in> ipv4s_to_set (ipv4_word_netmask_to_ipt_ipv4range ip) \<longleftrightarrow> simple_match_ip ip (p_src p)"
    "p_dst p \<in> ipv4s_to_set (ipv4_word_netmask_to_ipt_ipv4range ip) \<longleftrightarrow> simple_match_ip ip (p_dst p)"
apply(case_tac [!] ip)
apply(rename_tac b m)
by(simp_all add: bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary ipv4addr_of_dotteddecimal_dotteddecimal_of_ipv4addr)


lemma ports_to_set_singleton_simple_match_port: "p \<in> ports_to_set [a] \<longleftrightarrow> simple_match_port a p"
  by(cases a, simp)


theorem simple_match_to_ipportiface_match_correct: "matches (ipportiface_matcher, \<alpha>) (simple_match_to_ipportiface_match sm) a p \<longleftrightarrow> simple_matches sm p"
  apply(cases sm)
  apply(rename_tac iif oif sip dip pro sps dps)
  apply(simp add: bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary)
  apply(rule refl_conj_eq)+
  apply(simp add: matches_SrcDst_simple_match)
  apply(rule refl_conj_eq)+
(*brute force proof from here*)
apply(case_tac [!] sps)
apply(simp_all)
apply(case_tac [!] dps)
apply(simp_all)
done


subsection{*MatchExpr to Simple Match*}
(*Unfinished*)
text{*Unfinished*}

fun ipportiface_match_to_simple_match :: "ipportiface_rule_match match_expr \<Rightarrow> simple_match option" where
  "ipportiface_match_to_simple_match MatchAny = Some simple_match_any" |
  "ipportiface_match_to_simple_match (MatchNot MatchAny) = None" |
  "ipportiface_match_to_simple_match (Match (IIface iif)) = Some (simple_match_any\<lparr> iiface := iif \<rparr>)" |
  "ipportiface_match_to_simple_match (Match (OIface oif)) = Some (simple_match_any\<lparr> oiface := oif \<rparr>)" |
  "ipportiface_match_to_simple_match (Match (Src ip)) = Some (simple_match_any\<lparr> src := (ipt_ipv4range_to_ipv4_word_netmask ip) \<rparr>)" |
  "ipportiface_match_to_simple_match (Match (Dst ip)) = Some (simple_match_any\<lparr> dst := (ipt_ipv4range_to_ipv4_word_netmask ip) \<rparr>)" |
  "ipportiface_match_to_simple_match (Match (Prot p)) = Some (simple_match_any\<lparr> proto := p \<rparr>)" |
  "ipportiface_match_to_simple_match (Match (Src_Ports [])) = Some (simple_match_any)" |
  "ipportiface_match_to_simple_match (Match (Src_Ports [(s,e)])) = Some (simple_match_any\<lparr> sports := (s,e) \<rparr>)" |
  "ipportiface_match_to_simple_match (Match (Dst_Ports [])) = Some (simple_match_any)" |
  "ipportiface_match_to_simple_match (Match (Dst_Ports [(s,e)])) = Some (simple_match_any\<lparr> dports := (s,e) \<rparr>)" |
  (*"ipportiface_match_to_simple_match (MatchNot (Match (IIface IfaceAny))) = None" |*)
  "ipportiface_match_to_simple_match (MatchNot (Match (IIface (Iface (Pos eth))))) = Some (simple_match_any\<lparr> iiface := Iface (Neg eth) \<rparr>)" |
  "ipportiface_match_to_simple_match (MatchNot (Match (IIface (Iface (Neg eth))))) = Some (simple_match_any\<lparr> iiface := Iface (Pos eth) \<rparr>)" |
  (*"ipportiface_match_to_simple_match (MatchNot (Match (OIface IfaceAny))) = None" |*)
  "ipportiface_match_to_simple_match (MatchNot (Match (OIface (Iface (Pos eth))))) = Some (simple_match_any\<lparr> oiface := Iface (Neg eth) \<rparr>)" |
  "ipportiface_match_to_simple_match (MatchNot (Match (OIface (Iface (Neg eth))))) = Some (simple_match_any\<lparr> oiface := Iface (Pos eth) \<rparr>)" |
  "ipportiface_match_to_simple_match (MatchNot (Match (Prot ProtoAny))) = None" |
  "ipportiface_match_to_simple_match (MatchNot (Match (Prot (Proto (Pos p))))) =  Some (simple_match_any\<lparr> proto := Proto (Neg p) \<rparr>)" |
  "ipportiface_match_to_simple_match (MatchNot (Match (Prot (Proto (Neg p))))) =  Some (simple_match_any\<lparr> proto := Proto (Pos p) \<rparr>)" |
  --"TODO:"
  "ipportiface_match_to_simple_match (MatchAnd m1 m2) =  undefined" | (*TODO*)
  (*TODO: need to enable negation type again*)
  "ipportiface_match_to_simple_match (MatchNot (Match (Src ip))) = undefined" |
  "ipportiface_match_to_simple_match (MatchNot (Match (Dst ip))) = undefined" |
  --"undefined cases, normalize before!"
  "ipportiface_match_to_simple_match (MatchNot (MatchAnd _ _)) = undefined" |
  "ipportiface_match_to_simple_match (MatchNot (MatchNot _)) = undefined" |
  "ipportiface_match_to_simple_match (Match (Src_Ports (_#_))) = undefined" |
  "ipportiface_match_to_simple_match (Match (Dst_Ports (_#_))) = undefined" |
  "ipportiface_match_to_simple_match (MatchNot (Match (Src_Ports _))) = undefined" |
  "ipportiface_match_to_simple_match (MatchNot (Match (Dst_Ports _))) = undefined" |
  "ipportiface_match_to_simple_match (Match (Extra _)) = undefined" |
  "ipportiface_match_to_simple_match (MatchNot (Match (Extra _))) = undefined"
(*\<dots>*)

subsubsection{*Normalizing ports*}
  (*TODO: Move?*)

  fun ipt_ports_negation_type_normalize :: "ipt_ports negation_type \<Rightarrow> ipt_ports" where
    "ipt_ports_negation_type_normalize (Pos ps) = ps" |
    "ipt_ports_negation_type_normalize (Neg ps) = br2l (bitrange_invert (l2br ps))"  
  
  
  lemma "ipt_ports_negation_type_normalize (Neg [(0,65535)]) = []" by eval

  declare ipt_ports_negation_type_normalize.simps[simp del]
  
  lemma ipt_ports_negation_type_normalize_correct:
        "matches (ipportiface_matcher, \<alpha>) (negation_type_to_match_expr (Src_Ports) ps) a p \<longleftrightarrow>
         matches (ipportiface_matcher, \<alpha>) (Match (Src_Ports (ipt_ports_negation_type_normalize ps))) a p"
        "matches (ipportiface_matcher, \<alpha>) (negation_type_to_match_expr (Dst_Ports) ps) a p \<longleftrightarrow>
         matches (ipportiface_matcher, \<alpha>) (Match (Dst_Ports (ipt_ports_negation_type_normalize ps))) a p"
  apply(case_tac [!] ps)
  apply(simp_all add: ipt_ports_negation_type_normalize.simps matches_case_ternaryvalue_tuple
          bunch_of_lemmata_about_matches bool_to_ternary_simps l2br_br2l ports_to_set_bitrange split: ternaryvalue.split)
  done
  
  (* [ [(1,2) \<or> (3,4)]  \<and>  [] ]*)
  definition ipt_ports_andlist_compress :: "ipt_ports list \<Rightarrow> ipt_ports" where
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
  definition normalize_ports_step :: "((ipportiface_rule_match \<Rightarrow> bool) \<times> (ipportiface_rule_match \<Rightarrow> ipt_ports)) \<Rightarrow> 
                               (ipt_ports \<Rightarrow> ipportiface_rule_match) \<Rightarrow>
                               ipportiface_rule_match match_expr \<Rightarrow> ipportiface_rule_match match_expr list" where 
    "normalize_ports_step (disc_sel) C  m = (case primitive_extractor (disc_sel) m 
                of (spts, rst) \<Rightarrow> map (\<lambda>spt. (MatchAnd (Match (C [spt]))) rst) (ipt_ports_compress spts))"
  
  
  lemma normalize_ports_step_Src: assumes "normalized_match m" shows
        "match_list (ipportiface_matcher, \<alpha>) (normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports m) a p \<longleftrightarrow>
         matches (ipportiface_matcher, \<alpha>) m a p"
    proof -
      obtain as ms where pe: "primitive_extractor (is_Src_Ports, src_ports_sel) m = (as, ms)" by fastforce
      from pe have normalize_ports_step: "normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports m = 
            (map (\<lambda>spt. MatchAnd (Match (Src_Ports [spt])) ms) (ipt_ports_compress as))"
        by(simp add: normalize_ports_step_def)
      from pe  primitive_extractor_correct(1)[OF assms wf_disc_sel_ipportiface_rule_match(1), where \<gamma>="(ipportiface_matcher, \<alpha>)" and a=a and p=p] have 
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
      from pe  primitive_extractor_correct(1)[OF assms wf_disc_sel_ipportiface_rule_match(2), where \<gamma>="(ipportiface_matcher, \<alpha>)" and a=a and p=p] have 
        "matches (ipportiface_matcher, \<alpha>) m a p \<longleftrightarrow>
          (matches (ipportiface_matcher, \<alpha>) (alist_and (NegPos_map Dst_Ports as)) a p \<and> matches (ipportiface_matcher, \<alpha>) ms a p)"
      by simp
      also have "... \<longleftrightarrow> match_list (ipportiface_matcher, \<alpha>) (normalize_ports_step (is_Dst_Ports, dst_ports_sel) Dst_Ports m) a p"
        by(simp add: normalize_ports_step singletonize_SrcDst_Ports(2) bunch_of_lemmata_about_matches(1) ipt_ports_compress_dst_correct)
      finally show ?thesis by simp
    qed
  
  
  fun normalized_src_ports :: "ipportiface_rule_match match_expr \<Rightarrow> bool" where
    "normalized_src_ports MatchAny = True" |
    "normalized_src_ports (Match (Src_Ports [])) = True" |
    "normalized_src_ports (Match (Src_Ports [_])) = True" |
    "normalized_src_ports (Match (Src_Ports _)) = False" |
    "normalized_src_ports (Match _) = True" |
    "normalized_src_ports (MatchNot (Match (Src_Ports _))) = False" |
    "normalized_src_ports (MatchAnd m1 m2) = (normalized_src_ports m1 \<and> normalized_src_ports m2)" |
    "normalized_src_ports (MatchNot (MatchAnd _ _)) = False" |
    "normalized_src_ports (MatchNot _) = True"
  
  fun normalized_dst_ports :: "ipportiface_rule_match match_expr \<Rightarrow> bool" where
    "normalized_dst_ports MatchAny = True" |
    "normalized_dst_ports (Match (Dst_Ports [])) = True" |
    "normalized_dst_ports (Match (Dst_Ports [_])) = True" |
    "normalized_dst_ports (Match (Dst_Ports _)) = False" |
    "normalized_dst_ports (Match _) = True" |
    "normalized_dst_ports (MatchNot (Match (Dst_Ports _))) = False" |
    "normalized_dst_ports (MatchAnd m1 m2) = (normalized_dst_ports m1 \<and> normalized_dst_ports m2)" |
    "normalized_dst_ports (MatchNot (MatchAnd _ _)) = False" |
    "normalized_dst_ports (MatchNot _) = True" 
  
  (*unused? TODO: Move?*)
  lemma normalized_match_MatchNot_D: "normalized_match (MatchNot m) \<Longrightarrow> normalized_match m"
  apply(induction m)
  apply(simp_all)
  done
  
  
  lemma "\<forall>spt \<in> set (ipt_ports_compress spts). normalized_src_ports (Match (Src_Ports [spt]))" by(simp)
  

  lemma assumes normalize_ports_step_src_normalized: "normalized_match m"
    shows "\<forall>mn \<in> set (normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports m). normalized_src_ports mn \<and> normalized_match mn"
    proof
      fix mn
      assume assm2: "mn \<in> set (normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports m)"
      obtain pts ms where pts_ms: "primitive_extractor (is_Src_Ports, src_ports_sel) m = (pts, ms)" by fastforce
      from pts_ms have "normalized_match ms" and "\<not> has_disc is_Src_Ports ms"
        using primitive_extractor_correct[OF assms wf_disc_sel_ipportiface_rule_match(1)] by simp_all
      from assm2 pts_ms have normalize_ports_step_unfolded: "mn \<in> (\<lambda>spt. MatchAnd (Match (Src_Ports [spt])) ms) ` set (ipt_ports_compress pts)"
        unfolding normalize_ports_step_def by force
      with `normalized_match ms` have "normalized_match mn" by fastforce
      from `normalized_match ms` `\<not> has_disc is_Src_Ports ms` have "normalized_src_ports ms"
        by(induction ms rule: normalized_src_ports.induct, simp_all)
      from normalize_ports_step_unfolded this have "normalized_src_ports mn"
      by(induction pts) (fastforce)+
      with `normalized_match mn` show "normalized_src_ports mn \<and> normalized_match mn" by simp
    qed



subsubsection{*Merging Simple Matches*}
text{*@{typ "simple_match"} @{text \<and>} @{typ "simple_match"}*}




  (*Why option? once the negation_type is gone from the interfaces, we should be able to directly merge!*)
  fun simple_match_and :: "simple_match \<Rightarrow> simple_match \<Rightarrow> simple_match option" where
    "simple_match_and \<lparr>iiface=iif1, oiface=oif1, src=sip1, dst=dip1, proto=p1, sports=sps1, dports=dps1 \<rparr> 
                      \<lparr>iiface=iif2, oiface=oif2, src=sip2, dst=dip2, proto=p2, sports=sps2, dports=dps2 \<rparr> = 
      (case simple_ips_conjunct sip1 sip2 of None \<Rightarrow> None | Some sip \<Rightarrow> 
      (case simple_ips_conjunct dip1 dip2 of None \<Rightarrow> None | Some dip \<Rightarrow> 
      Some \<lparr>iiface=iif2, oiface=oif2, src=sip, dst=dip, proto=p2, sports=simpl_ports_conjunct sps1 sps2, dports=simpl_ports_conjunct sps1 sps2 \<rparr>))"
                      (*add list comprehension to multiply out the interface blowup? hopefully not necessary*)

end

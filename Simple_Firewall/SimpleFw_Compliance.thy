theory SimpleFw_Compliance
imports SimpleFw_Semantics "../Primitive_Matchers/IPPortIfaceSpace_Matcher" "../Semantics_Ternary" "../Output_Format/Negation_Type_Matching" "../Bitmagic/Numberwang_Ln"
begin

fun ipv4_word_netmask_to_ipt_ipv4range :: "(ipv4addr \<times> nat) \<Rightarrow> ipt_ipv4range" where
  "ipv4_word_netmask_to_ipt_ipv4range (ip, n) = Ip4AddrNetmask (dotteddecimal_of_ipv4addr ip) n"

fun ipt_ipv4range_to_ipv4_word_netmask :: " ipt_ipv4range \<Rightarrow> (ipv4addr \<times> nat)" where
  "ipt_ipv4range_to_ipv4_word_netmask (Ip4Addr ip_ddecim) = (ipv4addr_of_dotteddecimal ip_ddecim, 32)" | 
  "ipt_ipv4range_to_ipv4_word_netmask (Ip4AddrNetmask ip_ddecim n) = (ipv4addr_of_dotteddecimal ip_ddecim, n)"

(*do I need monads?*)
fun negation_type_to_match_expr :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a negation_type \<Rightarrow> 'b match_expr" where
  "negation_type_to_match_expr f (Pos a) = Match (f a)" |
  "negation_type_to_match_expr f (Neg a) = MatchNot (Match (f a))"

fun simple_match_to_ipportiface_match :: "simple_match \<Rightarrow> ipportiface_rule_match match_expr" where
  "simple_match_to_ipportiface_match \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr> = 
    MatchAnd (Match (IIface iif)) (MatchAnd (Match (OIface oif)) 
    (MatchAnd (negation_type_to_match_expr (\<lambda>x. Src (ipv4_word_netmask_to_ipt_ipv4range x)) sip )
    (MatchAnd (negation_type_to_match_expr (\<lambda>x. Dst (ipv4_word_netmask_to_ipt_ipv4range x)) dip )
    (MatchAnd (Match (Prot p))
    (MatchAnd (Match (Src_Ports [sps]))
    (Match (Dst_Ports [dps]))
    )))))"



(*is this usefull?*)
lemma xxx: "matches \<gamma> (simple_match_to_ipportiface_match \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr>) a p \<longleftrightarrow> 
      matches \<gamma> (alist_and ([Pos (IIface iif), Pos (OIface oif)] @ (NegPos_map (Src \<circ> ipv4_word_netmask_to_ipt_ipv4range) [sip])
        @ (NegPos_map (Dst \<circ> ipv4_word_netmask_to_ipt_ipv4range) [dip]) @ [Pos (Prot p)]
        @ [Pos (Src_Ports [sps])] @ [Pos (Dst_Ports [dps])])) a p"
apply(simp add:)
apply(cases sip)
apply(simp_all)
apply(case_tac [!] dip)
apply(simp_all)
apply(simp_all add: bunch_of_lemmata_about_matches)
done

(*TODO: smelly duplication*)
lemma matches_Src_simple_match: "matches (ipportiface_matcher, \<alpha>) (negation_type_to_match_expr (\<lambda>x. ipportiface_rule_match.Src (ipv4_word_netmask_to_ipt_ipv4range x)) ip) a p \<longleftrightarrow>
  simple_match_ip ip (p_src p)"
apply(cases ip)
 apply(rename_tac i_ip)
 apply(case_tac i_ip)
 apply(rename_tac iip n)
 apply(simp add: bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary ipv4addr_of_dotteddecimal_dotteddecimal_of_ipv4addr)
apply(simp)
apply(rename_tac i_ip)
apply(case_tac i_ip)
apply(rename_tac iip n)
apply(simp add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)
apply(simp add: bunch_of_lemmata_about_matches bool_to_ternary_simps ipv4addr_of_dotteddecimal_dotteddecimal_of_ipv4addr)
done
lemma matches_Dst_simple_match: "matches (ipportiface_matcher, \<alpha>) (negation_type_to_match_expr (\<lambda>x. ipportiface_rule_match.Dst (ipv4_word_netmask_to_ipt_ipv4range x)) ip) a p \<longleftrightarrow>
  simple_match_ip ip (p_dst p)"
apply(cases ip)
 apply(rename_tac i_ip)
 apply(case_tac i_ip)
 apply(rename_tac iip n)
 apply(simp add: bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary ipv4addr_of_dotteddecimal_dotteddecimal_of_ipv4addr)
apply(simp)
apply(rename_tac i_ip)
apply(case_tac i_ip)
apply(rename_tac iip n)
apply(simp add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)
apply(simp add: bunch_of_lemmata_about_matches bool_to_ternary_simps ipv4addr_of_dotteddecimal_dotteddecimal_of_ipv4addr)
done


lemma ports_to_set_singleton_simple_match_port: "p \<in> ports_to_set [a] \<longleftrightarrow> simple_match_port a p"
  by(cases a, simp)


lemma "matches (ipportiface_matcher, \<alpha>) (simple_match_to_ipportiface_match sm) a p \<longleftrightarrow> simple_matches sm p"
  apply(cases sm)
  apply(rename_tac iif oif sip dip pro sps dps)
  apply(simp add: bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary)
  apply(rule refl_conj_eq)+
  apply(simp add: matches_Src_simple_match matches_Dst_simple_match)
  apply(rule refl_conj_eq)+
(*brute force proof from here*)
apply(case_tac [!] sps)
apply(simp_all)
apply(case_tac [!] dps)
apply(simp_all)
done


thm normalized_match.simps

fun ipportiface_match_to_simple_match :: "ipportiface_rule_match match_expr \<Rightarrow> simple_match" where
  "ipportiface_match_to_simple_match (Match (IIface iif)) = simple_match_any\<lparr> iiface := iif \<rparr>" |
  "ipportiface_match_to_simple_match (Match (OIface oif)) = simple_match_any\<lparr> oiface := oif \<rparr>" |
  "ipportiface_match_to_simple_match (Match (Src ip)) = simple_match_any\<lparr> src := Pos (ipt_ipv4range_to_ipv4_word_netmask ip) \<rparr>" |
  "ipportiface_match_to_simple_match (Match (Dst ip)) = simple_match_any\<lparr> dst := Pos (ipt_ipv4range_to_ipv4_word_netmask ip) \<rparr>" |
  "ipportiface_match_to_simple_match (Match (Prot p)) = simple_match_any\<lparr> proto := p \<rparr>" |
  "ipportiface_match_to_simple_match (Match (Src_Ports [])) = simple_match_any" |
  "ipportiface_match_to_simple_match (Match (Src_Ports [(s,e)])) = simple_match_any\<lparr> sports := (s,e) \<rparr>" |
  "ipportiface_match_to_simple_match (Match (Dst_Ports [])) = simple_match_any" |
  "ipportiface_match_to_simple_match (Match (Dst_Ports [(s,e)])) = simple_match_any\<lparr> dports := (s,e) \<rparr>" |
  "ipportiface_match_to_simple_match (MatchNot (Match (Src ip))) = simple_match_any\<lparr> src := Neg (ipt_ipv4range_to_ipv4_word_netmask ip) \<rparr>" |
  "ipportiface_match_to_simple_match (MatchNot (Match (Dst ip))) = simple_match_any\<lparr> dst := Neg (ipt_ipv4range_to_ipv4_word_netmask ip) \<rparr>" |
  --"undefined cases, normalize before!"
  "ipportiface_match_to_simple_match (Match (Src_Ports (_#_))) = undefined" |
  "ipportiface_match_to_simple_match (Match (Dst_Ports (_#_))) = undefined" |
  "ipportiface_match_to_simple_match (Match (Extra _)) = undefined"
  (* hmm, port list (\<or>) to one port, creates multiple rules! need normalize_ports for match_Expr*)
(*\<dots>*)



(*TODO: Move?*)
fun ipt_ports_negation_type_normalize :: "ipt_ports negation_type \<Rightarrow> ipt_ports" where
  "ipt_ports_negation_type_normalize (Pos ps) = ps" |
  "ipt_ports_negation_type_normalize (Neg ps) = br2l (bitrange_invert (l2br ps))"



(*warning!! an empty port range means it can never match! no port range matches (corresponds to firewall behavior, but usually you cannot specify an empty portrange here)*)
lemma "ipt_ports_negation_type_normalize (Neg [(0,65535)]) = []" by eval
lemma "\<not> matches (ipportiface_matcher, \<alpha>) (MatchNot (Match (Src_Ports [(0,65535)]))) a 
        \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotteddecimal (192,168,2,45), p_dst= ipv4addr_of_dotteddecimal (173,194,112,111),
                 p_proto=TCP, p_sport=2065, p_dport=80\<rparr>"
by(simp add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)
lemma "matches (ipportiface_matcher, \<alpha>) (MatchNot (Match (Src_Ports []))) a 
        \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotteddecimal (192,168,2,45), p_dst= ipv4addr_of_dotteddecimal (173,194,112,111),
                 p_proto=TCP, p_sport=2065, p_dport=80\<rparr>"
by(simp add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)
lemma "\<not>matches (ipportiface_matcher, \<alpha>) (MatchNot (Match (Src_Ports [(1024,4096)]))) a 
        \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotteddecimal (192,168,2,45), p_dst= ipv4addr_of_dotteddecimal (173,194,112,111),
                 p_proto=TCP, p_sport=2065, p_dport=80\<rparr>"
by(simp add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)



declare ipt_ports_negation_type_normalize.simps[simp del]

lemma ipt_ports_negation_type_normalize_correct:
      "matches (ipportiface_matcher, \<alpha>) (negation_type_to_match_expr (Src_Ports) ps) a p \<longleftrightarrow>
       matches (ipportiface_matcher, \<alpha>) (Match (Src_Ports (ipt_ports_negation_type_normalize ps))) a p"
      "matches (ipportiface_matcher, \<alpha>) (negation_type_to_match_expr (Dst_Ports) ps) a p \<longleftrightarrow>
       matches (ipportiface_matcher, \<alpha>) (Match (Dst_Ports (ipt_ports_negation_type_normalize ps))) a p"
apply(case_tac [!] ps)
apply(simp_all add: ipt_ports_negation_type_normalize.simps matches_case_ternaryvalue_tuple bunch_of_lemmata_about_matches bool_to_ternary_simps l2br_br2l ports_to_set_bitrange split: ternaryvalue.split)
done

(*todo: move*)
value "primitive_extractor (is_Src_Ports, src_ports_sel) m"

term fold
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
        by(simp add: ipt_ports_compress_def ipt_ports_andlist_compress_correct bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary ipt_ports_negation_type_normalize.simps)
      next
      case (Neg a)
        thus ?goal using Cons.IH
        apply(simp add: ipt_ports_compress_def ipt_ports_andlist_compress_correct bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary)
        apply(simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps l2br_br2l ports_to_set_bitrange ipt_ports_negation_type_normalize.simps split: ternaryvalue.split)
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
        by(simp add: ipt_ports_compress_def ipt_ports_andlist_compress_correct bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary ipt_ports_negation_type_normalize.simps)
      next
      case (Neg a)
        thus ?goal using Cons.IH
        apply(simp add: ipt_ports_compress_def ipt_ports_andlist_compress_correct bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary)
        apply(simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps l2br_br2l ports_to_set_bitrange ipt_ports_negation_type_normalize.simps split: ternaryvalue.split)
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

(*normalizing source ports, only at most one source port will exist in the match expression. better proof and formalization below*)
lemma "normalized_match m \<Longrightarrow> 
      match_list (ipportiface_matcher, \<alpha>) (case primitive_extractor (is_Src_Ports, src_ports_sel) m 
        of (spts, rst) \<Rightarrow> map (\<lambda>spt. (MatchAnd (Match (Src_Ports [spt]))) rst) (ipt_ports_compress spts)) a p \<longleftrightarrow>
       matches (ipportiface_matcher, \<alpha>) m a p"
  apply(case_tac "primitive_extractor (is_Src_Ports, src_ports_sel) m")
  apply(rename_tac as ms)
  apply(simp)
  apply(drule(1) primitive_extractor_correct(1)[OF _ wf_disc_sel_ipportiface_rule_match(1), where \<gamma>="(ipportiface_matcher, \<alpha>)" and a=a and p=p])
  apply(drule sym) back (*WHOOOOO*)
  apply(simp)
  apply(simp add: singletonize_SrcDst_Ports)
  apply(simp add: bunch_of_lemmata_about_matches(1))
  apply(simp add: ipt_ports_compress_src_correct)
done

definition normalize_ports_step :: "((ipportiface_rule_match \<Rightarrow> bool) \<times> (ipportiface_rule_match \<Rightarrow> ipt_ports)) \<Rightarrow> 
                             (ipt_ports \<Rightarrow> ipportiface_rule_match) \<Rightarrow>
                             ipportiface_rule_match match_expr \<Rightarrow> ipportiface_rule_match match_expr list" where 
  "normalize_ports_step (disc_sel) C  m = (case primitive_extractor (disc_sel) m 
              of (spts, rst) \<Rightarrow> map (\<lambda>spt. (MatchAnd (Match (C [spt]))) rst) (ipt_ports_compress spts))"


(*normalizing source ports, only at most one source port will exist in the match expression.*)
lemma normalize_ports_step_Src: assumes "normalized_match m" shows
      "match_list (ipportiface_matcher, \<alpha>) (normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports m) a p \<longleftrightarrow>
       matches (ipportiface_matcher, \<alpha>) m a p"
  proof -
    obtain as ms where pe: "primitive_extractor (is_Src_Ports, src_ports_sel) m = (as, ms)" by fastforce
    from pe have normalize_ports_step: "normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports m = (map (\<lambda>spt. MatchAnd (Match (Src_Ports [spt])) ms) (ipt_ports_compress as))"
      by(simp add: normalize_ports_step_def)
    from pe  primitive_extractor_correct(1)[OF assms wf_disc_sel_ipportiface_rule_match(1), where \<gamma>="(ipportiface_matcher, \<alpha>)" and a=a and p=p] have 
      "matches (ipportiface_matcher, \<alpha>) m a p \<longleftrightarrow> (matches (ipportiface_matcher, \<alpha>) (alist_and (NegPos_map Src_Ports as)) a p \<and> matches (ipportiface_matcher, \<alpha>) ms a p)"
    by simp
    also have "... \<longleftrightarrow> match_list (ipportiface_matcher, \<alpha>) (normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports m) a p"
      by(simp add: normalize_ports_step singletonize_SrcDst_Ports(1) bunch_of_lemmata_about_matches(1) ipt_ports_compress_src_correct)
    finally show ?thesis by simp
  qed

lemma "normalized_match m \<Longrightarrow> 
      match_list (ipportiface_matcher, \<alpha>) (normalize_ports_step (is_Dst_Ports, dst_ports_sel) Dst_Ports m) a p \<longleftrightarrow>
       matches (ipportiface_matcher, \<alpha>) m a p"
  unfolding normalize_ports_step_def
  apply(case_tac "primitive_extractor (is_Dst_Ports, dst_ports_sel) m")
  apply(rename_tac as ms)
  apply(simp)
  apply(drule(1) primitive_extractor_correct(1)[OF _ wf_disc_sel_ipportiface_rule_match(2), where \<gamma>="(ipportiface_matcher, \<alpha>)" and a=a and p=p])
  apply(drule sym) back (*WHOOOOO*)
  apply(simp)
  apply(simp add: singletonize_SrcDst_Ports(2))
  apply(simp add: bunch_of_lemmata_about_matches(1))
  apply(simp add: ipt_ports_compress_dst_correct)
done


(*TODO*)
fun normalized_ports :: "ipportiface_rule_match match_expr \<Rightarrow> bool" where
  "normalized_ports MatchAny = True" |
  "normalized_ports (Match (Src_Ports [])) = True" |
  "normalized_ports (Match (Src_Ports [_])) = True" |
  "normalized_ports (Match (Src_Ports _)) = False" |
  (* "normalized_ports (Match (Dst_Ports [])) = True" | *)
  "normalized_ports (Match _) = True" |
  "normalized_ports (MatchNot (Match (Src_Ports _))) = False" |
  "normalized_ports (MatchAnd m1 m2) = (normalized_ports m1 \<and> normalized_ports m2)" |
  "normalized_ports (MatchNot (MatchAnd _ _)) = False" |
  "normalized_ports (MatchNot _) = True" 

lemma normalized_match_MatchNot_D: "normalized_match (MatchNot m) \<Longrightarrow> normalized_match ( m) "
apply(induction m)
apply(simp_all)
done


lemma "\<forall>spt \<in> set (ipt_ports_compress spts). normalized_ports (Match (Src_Ports [spt]))" by(simp)

lemma help1: "normalized_match ms \<Longrightarrow> \<not> has_disc is_Src_Ports ms \<Longrightarrow> normalized_ports ms"
  apply(induction ms rule: normalized_ports.induct)
  apply(simp_all)
  done

lemma "normalized_match m \<Longrightarrow> 
      primitive_extractor (is_Src_Ports, src_ports_sel) m = (spts, ms) \<Longrightarrow>
      ml \<in> set (map (\<lambda>spt. (MatchAnd (Match (Src_Ports [spt]))) ms) (ipt_ports_compress spts))\<Longrightarrow>
      normalized_ports ml"
apply(simp)
apply(frule(1) primitive_extractor_correct(2)[OF _ wf_disc_sel_ipportiface_rule_match(1)])
apply(frule(1) primitive_extractor_correct(3)[OF _ wf_disc_sel_ipportiface_rule_match(1)])
apply(simp add: ipt_ports_compress_def)
apply(drule(1) help1)
apply(induction spts)
 apply(clarsimp)+
done



end

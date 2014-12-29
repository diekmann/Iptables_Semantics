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
    (MatchAnd (negation_type_to_match_expr (\<lambda>x. Src_Ports [x]) sps)
    (negation_type_to_match_expr (\<lambda>x. Dst_Ports [x]) dps)
    )))))"



(*is this usefull?*)
lemma xxx: "matches \<gamma> (simple_match_to_ipportiface_match \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr>) a p \<longleftrightarrow> 
      matches \<gamma> (alist_and ([Pos (IIface iif), Pos (OIface oif)] @ (NegPos_map (Src \<circ> ipv4_word_netmask_to_ipt_ipv4range) [sip])
        @ (NegPos_map (Dst \<circ> ipv4_word_netmask_to_ipt_ipv4range) [dip]) @ [Pos (Prot p)]
        @ (NegPos_map (\<lambda>x. Src_Ports [x]) [sps]) @ (NegPos_map (\<lambda>x. Dst_Ports [x]) [dps]))) a p"
apply(simp add:)
apply(cases sip)
apply(simp_all)
apply(case_tac [!] dip)
apply(simp_all)
apply(case_tac [!] sps)
apply(simp_all)
apply(case_tac [!] dps)
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


lemma ports_to_set_singleton_simple_match_port: "p \<in> ports_to_set [a] \<longleftrightarrow> simple_match_port (Pos a) p"
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
apply(simp_all add: bunch_of_lemmata_about_matches eval_ternary_simps ternary_to_bool_bool_to_ternary)
apply(simp_all add: ports_to_set_singleton_simple_match_port)
apply(auto simp add: matches_case_ternaryvalue_tuple bunch_of_lemmata_about_matches bool_to_ternary_simps split: ternaryvalue.split) (* oh dear, sorry for that *)
done


thm normalized_match.simps

fun ipportiface_match_to_simple_match :: "ipportiface_rule_match match_expr \<Rightarrow> simple_match" where
  "ipportiface_match_to_simple_match (Match (IIface iif)) = simple_match_any\<lparr> iiface := iif \<rparr>" |
  "ipportiface_match_to_simple_match (Match (OIface oif)) = simple_match_any\<lparr> oiface := oif \<rparr>" |
  "ipportiface_match_to_simple_match (Match (Src ip)) = simple_match_any\<lparr> src := Pos (ipt_ipv4range_to_ipv4_word_netmask ip) \<rparr>" |
  "ipportiface_match_to_simple_match (Match (Dst ip)) = simple_match_any\<lparr> dst := Pos (ipt_ipv4range_to_ipv4_word_netmask ip) \<rparr>" |
  "ipportiface_match_to_simple_match (Match (Prot p)) = simple_match_any\<lparr> proto := p \<rparr>"|
  "ipportiface_match_to_simple_match (Match (Src_Ports ps)) = simple_match_any\<lparr> sports := Pos (0,0) \<rparr>"
  (* hmm, port list (\<or>) to one port, creates multiple rules! need normalize_ports for match_Expr*)
(*\<dots>*)



(*TODO: Move?*)
fun ipt_ports_negation_type_normalize :: "ipt_ports negation_type \<Rightarrow> ipt_ports" where
  "ipt_ports_negation_type_normalize (Pos ps) = ps" |
  "ipt_ports_negation_type_normalize (Neg ps) = br2l (bitrange_invert (l2br ps))"

lemma ipt_ports_negation_type_normalize_correct:
      "matches (ipportiface_matcher, \<alpha>) (negation_type_to_match_expr (Src_Ports) ps) a p \<longleftrightarrow>
       matches (ipportiface_matcher, \<alpha>) (Match (Src_Ports (ipt_ports_negation_type_normalize ps))) a p"
      "matches (ipportiface_matcher, \<alpha>) (negation_type_to_match_expr (Dst_Ports) ps) a p \<longleftrightarrow>
       matches (ipportiface_matcher, \<alpha>) (Match (Dst_Ports (ipt_ports_negation_type_normalize ps))) a p"
apply(case_tac [!] ps)
apply(simp_all add: matches_case_ternaryvalue_tuple bunch_of_lemmata_about_matches bool_to_ternary_simps l2br_br2l ports_to_set_bitrange split: ternaryvalue.split)
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

(**TODO: combine proofs to alist_and**)
find_consts "'b list \<Rightarrow> 'a match_expr"


fun ipt_ports_compress :: "ipt_ports negation_type list \<Rightarrow> ipt_ports" where
  "ipt_ports_compress (ps#pss) = (ipt_ports_negation_type_normalize ps)"

value "case primitive_extractor (is_Src_Ports, src_ports_sel) m 
        of (spts, rst) \<Rightarrow> map (\<lambda>spt. (MatchAnd (Match (Src_Ports [spt]))) rst) (merge_ipt_ports spts)"

fun normalize_ipt_ports :: "ipportiface_rule_match match_expr \<Rightarrow> ipportiface_rule_match match_expr list" where
  "normalize_ipt_ports (Match (Src_Ports [])) = []" |
  "normalize_ipt_ports (Match (Src_Ports (p#ps))) = []"

end

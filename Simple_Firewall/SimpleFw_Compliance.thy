theory SimpleFw_Compliance
imports SimpleFw_Semantics "../Primitive_Matchers/IPPortIfaceSpace_Matcher" "../Semantics_Ternary" "../Output_Format/Negation_Type_Matching" "../Bitmagic/Numberwang_Ln"
begin

fun ipv4_word_netmask_to_nattuple :: "(ipv4addr \<times> nat)  \<Rightarrow> ipt_ipv4range" where
  "ipv4_word_netmask_to_nattuple (ip, n) = Ip4AddrNetmask (dotteddecimal_of_ipv4addr ip) n"

fun negation_type_to_match_expr :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a negation_type \<Rightarrow> 'b match_expr" where
  "negation_type_to_match_expr f (Pos a) = Match (f a)" |
  "negation_type_to_match_expr f (Neg a) = MatchNot (Match (f a))"

fun simple_match_to_ipportiface_match :: "simple_match \<Rightarrow> ipportiface_rule_match match_expr" where
  "simple_match_to_ipportiface_match \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr> = 
    MatchAnd (Match (IIface iif)) (MatchAnd (Match (OIface oif)) 
    (MatchAnd (negation_type_to_match_expr (\<lambda>x. Src (ipv4_word_netmask_to_nattuple x)) sip )
    (MatchAnd (negation_type_to_match_expr (\<lambda>x. Dst (ipv4_word_netmask_to_nattuple x)) dip )
    (MatchAnd (Match (Prot p))
    (MatchAnd (negation_type_to_match_expr (\<lambda>x. Src_Ports [x]) sps)
    (negation_type_to_match_expr (\<lambda>x. Dst_Ports [x]) dps)
    )))))"



(*is this usefull?*)
lemma xxx: "matches \<gamma> (simple_match_to_ipportiface_match \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr>) a p \<longleftrightarrow> 
      matches \<gamma> (alist_and ([Pos (IIface iif), Pos (OIface oif)] @ (NegPos_map (Src \<circ> ipv4_word_netmask_to_nattuple) [sip])
        @ (NegPos_map (Dst \<circ> ipv4_word_netmask_to_nattuple) [dip]) @ [Pos (Prot p)]
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
lemma matches_Src_simple_match: "matches (ipportiface_matcher, \<alpha>) (negation_type_to_match_expr (\<lambda>x. ipportiface_rule_match.Src (ipv4_word_netmask_to_nattuple x)) ip) a p \<longleftrightarrow>
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
lemma matches_Dst_simple_match: "matches (ipportiface_matcher, \<alpha>) (negation_type_to_match_expr (\<lambda>x. ipportiface_rule_match.Dst (ipv4_word_netmask_to_nattuple x)) ip) a p \<longleftrightarrow>
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

end

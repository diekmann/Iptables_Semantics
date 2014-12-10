theory SimpleFw_Compliance
imports SimpleFw_Semantics "../Primitive_Matchers/IPPortIfaceSpace_Matcher" "../Semantics_Ternary"
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

lemma "matches (ipportiface_matcher, \<alpha>) (simple_match_to_ipportiface_match sm) a p \<longleftrightarrow> simple_matches sm p"
  apply(simp add: matches_case_ternaryvalue_tuple bool_to_ternary_Unknown bool_to_ternary_simps split: ternaryvalue.split)
  apply(cases sm)
  thm eval_ternary_simps bool_to_ternary_simps
  (*TODO*: ternary_ternary_eval_simps*)
  apply(safe)

end

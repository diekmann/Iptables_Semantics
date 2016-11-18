theory Common_Primitive_Matcher_Generic
imports "../Semantics_Ternary/Semantics_Ternary"
        Common_Primitive_Syntax
        "../Semantics_Ternary/Unknown_Match_Tacs"
begin


subsection\<open>A Generic primitive matcher: Agnostic of IP Addresses\<close>

text\<open>Generalized Definition agnostic of IP Addresses fro IPv4 and IPv6\<close>


(*generic assumptions for a common matcher without information about IPs.
  used to add ipv6 integration without duplicating all proofs *)
locale primitive_matcher_generic =
  fixes \<beta> :: "('i::len common_primitive, ('i::len, 'a) tagged_packet_scheme) exact_match_tac"
  assumes IIface: "\<forall> p i. \<beta> (IIface i) p = bool_to_ternary (match_iface i (p_iiface p))"
      and OIface: "\<forall> p i. \<beta> (OIface i) p = bool_to_ternary (match_iface i (p_oiface p))"
        and Prot: "\<forall> p proto. \<beta> (Prot proto) p = bool_to_ternary (match_proto proto (p_proto p))"
   and Src_Ports: "\<forall> p proto ps. \<beta> (Src_Ports (L4Ports proto ps)) p = bool_to_ternary (proto = p_proto p \<and> p_sport p \<in> ports_to_set ps)"
   and Dst_Ports: "\<forall> p proto ps. \<beta> (Dst_Ports (L4Ports proto ps)) p = bool_to_ternary (proto = p_proto p \<and> p_dport p \<in> ports_to_set ps)"
   -- "-m multiport --ports matches source or destination port"
   and MultiportsPorts: "\<forall> p proto ps. \<beta> (MultiportPorts (L4Ports proto ps)) p = bool_to_ternary (proto = p_proto p \<and> (p_sport p \<in> ports_to_set ps \<or> p_dport p \<in> ports_to_set ps))"
    and L4_Flags: "\<forall> p flags. \<beta> (L4_Flags flags) p = bool_to_ternary (match_tcp_flags flags (p_tcp_flags p))"
    and CT_State: "\<forall> p S. \<beta> (CT_State S) p = bool_to_ternary (match_ctstate S (p_tag_ctstate p))"
        and Extra: "\<forall> p str. \<beta> (Extra str) p = TernaryUnknown"
begin
  lemma Iface_single:
    "matches (\<beta>, \<alpha>) (Match (IIface X)) a p \<longleftrightarrow> match_iface X (p_iiface p)"
    "matches (\<beta>, \<alpha>) (Match (OIface X)) a p \<longleftrightarrow> match_iface X (p_oiface p)"
     by(simp_all add: IIface OIface match_raw_ternary bool_to_ternary_simps
               split: ternaryvalue.split)
  text\<open>Since matching on the iface cannot be @{const TernaryUnknown}*, we can pull out negations.\<close>
  lemma Iface_single_not:
    "matches (\<beta>, \<alpha>) (MatchNot (Match (IIface X))) a p \<longleftrightarrow> \<not> match_iface X (p_iiface p)"
    "matches (\<beta>, \<alpha>) (MatchNot (Match (OIface X))) a p \<longleftrightarrow> \<not> match_iface X (p_oiface p)"
     by(simp_all add: IIface OIface matches_case_ternaryvalue_tuple bool_to_ternary_simps
          split: ternaryvalue.split)

  lemma Prot_single:
    "matches (\<beta>, \<alpha>) (Match (Prot X)) a p \<longleftrightarrow> match_proto X (p_proto p)"
     by(simp add: Prot match_raw_ternary bool_to_ternary_simps split: ternaryvalue.split)
  lemma Prot_single_not:
    "matches (\<beta>, \<alpha>) (MatchNot (Match (Prot X))) a p \<longleftrightarrow> \<not> match_proto X (p_proto p)"
     by(simp add: Prot matches_case_ternaryvalue_tuple bool_to_ternary_simps split: ternaryvalue.split)

  lemma Ports_single:
    "matches (\<beta>, \<alpha>) (Match (Src_Ports (L4Ports proto ps))) a p \<longleftrightarrow> proto = p_proto p \<and> p_sport p \<in> ports_to_set ps"
    "matches (\<beta>, \<alpha>) (Match (Dst_Ports (L4Ports proto ps))) a p \<longleftrightarrow> proto = p_proto p \<and> p_dport p \<in> ports_to_set ps"
     by(simp_all add: Src_Ports Dst_Ports match_raw_ternary bool_to_ternary_simps
               split: ternaryvalue.split)
  lemma Ports_single_not:
    "matches (\<beta>, \<alpha>) (MatchNot (Match (Src_Ports (L4Ports proto ps)))) a p \<longleftrightarrow> proto \<noteq> p_proto p \<or> p_sport p \<notin> ports_to_set ps"
    "matches (\<beta>, \<alpha>) (MatchNot (Match (Dst_Ports (L4Ports proto ps)))) a p \<longleftrightarrow> proto \<noteq> p_proto p \<or> p_dport p \<notin> ports_to_set ps"
     by(simp_all add: Src_Ports Dst_Ports matches_case_ternaryvalue_tuple bool_to_ternary_simps
               split: ternaryvalue.split)

  text\<open>Ports are dependent matches. They always match on the protocol too\<close>
  lemma Ports_single_rewrite_Prot:
    "matches (\<beta>, \<alpha>) (Match (Src_Ports (L4Ports proto ps))) a p \<longleftrightarrow>
      matches (\<beta>, \<alpha>) (Match (Prot (Proto proto))) a p \<and> p_sport p \<in> ports_to_set ps"
    "matches (\<beta>, \<alpha>) (MatchNot (Match (Src_Ports (L4Ports proto ps)))) a p \<longleftrightarrow>
      matches (\<beta>, \<alpha>) (MatchNot (Match (Prot (Proto proto)))) a p \<or> p_sport p \<notin> ports_to_set ps"
    "matches (\<beta>, \<alpha>) (Match (Dst_Ports (L4Ports proto ps))) a p \<longleftrightarrow>
      matches (\<beta>, \<alpha>) (Match (Prot (Proto proto))) a p \<and> p_dport p \<in> ports_to_set ps"
    "matches (\<beta>, \<alpha>) (MatchNot (Match (Dst_Ports (L4Ports proto ps)))) a p \<longleftrightarrow>
      matches (\<beta>, \<alpha>) (MatchNot (Match (Prot (Proto proto)))) a p \<or> p_dport p \<notin> ports_to_set ps"
  by(auto simp add: Ports_single_not Ports_single Prot_single_not Prot_single)


  lemma multiports_disjuction:
        "(\<exists>rg\<in>set spts. matches (\<beta>, \<alpha>) (Match (Src_Ports (L4Ports proto [rg]))) a p) \<longleftrightarrow> matches (\<beta>, \<alpha>) (Match (Src_Ports (L4Ports proto spts))) a p"
        "(\<exists>rg\<in>set dpts. matches (\<beta>, \<alpha>) (Match (Dst_Ports (L4Ports proto [rg]))) a p) \<longleftrightarrow> matches (\<beta>, \<alpha>) (Match (Dst_Ports (L4Ports proto dpts))) a p"
    by(auto simp add: Src_Ports Dst_Ports match_raw_ternary bool_to_ternary_simps ports_to_set
                   split: ternaryvalue.split)

  lemma MultiportPorts_single_rewrite:
    "matches (\<beta>, \<alpha>) (Match (MultiportPorts ports)) a p \<longleftrightarrow>
      matches (\<beta>, \<alpha>) (Match (Src_Ports ports)) a p \<or> matches (\<beta>, \<alpha>) (Match (Dst_Ports ports)) a p"
    apply(cases ports)
    apply(simp add: Ports_single)
    by(simp add: MultiportsPorts match_raw_ternary bool_to_ternary_simps
            split: ternaryvalue.split)
  lemma MultiportPorts_single_rewrite_MatchOr:
    "matches (\<beta>, \<alpha>) (Match (MultiportPorts ports)) a p \<longleftrightarrow>
      matches (\<beta>, \<alpha>) (MatchOr (Match (Src_Ports ports)) (Match (Dst_Ports ports))) a p"
    apply(cases ports)
    by(simp add: MatchOr MultiportPorts_single_rewrite)

  lemma MultiportPorts_single_not_rewrite_MatchAnd:
    "matches (\<beta>, \<alpha>) (MatchNot (Match (MultiportPorts ports))) a p \<longleftrightarrow>
      matches (\<beta>, \<alpha>) (MatchAnd (MatchNot (Match (Src_Ports ports))) (MatchNot (Match (Dst_Ports ports)))) a p"
    apply(cases ports)
    apply(simp add: Ports_single_not bunch_of_lemmata_about_matches)
    by(simp add: MultiportsPorts matches_case_ternaryvalue_tuple bool_to_ternary_simps
            split: ternaryvalue.split)
  lemma MultiportPorts_single_not_rewrite:
    "matches (\<beta>, \<alpha>) (MatchNot (Match (MultiportPorts ports))) a p \<longleftrightarrow>
      \<not> matches (\<beta>, \<alpha>) (Match (Src_Ports ports)) a p \<and> \<not> matches (\<beta>, \<alpha>) (Match (Dst_Ports ports)) a p"
    apply(cases ports)
    by(simp add: MultiportPorts_single_not_rewrite_MatchAnd bunch_of_lemmata_about_matches
                 Ports_single_not Ports_single)


  lemma Extra_single:
    "matches (\<beta>, \<alpha>) (Match (Extra str)) a p \<longleftrightarrow> \<alpha> a p"
     by(simp add: Extra match_raw_ternary)
  lemma Extra_single_not:  --\<open>ternary logic, @{text "\<not> unknown = unknown"}\<close>
    "matches (\<beta>, \<alpha>) (MatchNot (Match (Extra str))) a p \<longleftrightarrow> \<alpha> a p"
     by(simp add: Extra matches_case_ternaryvalue_tuple)
end





subsection\<open>Basic optimisations\<close>
  
  (*this is currently not used.*)
  text\<open>Compress many @{const Extra} expressions to one expression.\<close>
  fun compress_extra :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr" where
    "compress_extra (Match x) = Match x" |
    "compress_extra (MatchNot (Match (Extra e))) = Match (Extra (''NOT (''@e@'')''))" |
    "compress_extra (MatchNot m) = (MatchNot (compress_extra m))" |
    (*"compress_extra (MatchAnd (Match (Extra e1)) (Match (Extra e2))) = compress_extra (Match (Extra (e1@'' ''@e2)))" |*)
    (*"compress_extra (MatchAnd (Match (Extra e1)) MatchAny) = Match (Extra e1)" |*)
    "compress_extra (MatchAnd (Match (Extra e1)) m2) = (case compress_extra m2 of Match (Extra e2) \<Rightarrow> Match (Extra (e1@'' ''@e2)) | MatchAny \<Rightarrow> Match (Extra e1) | m2' \<Rightarrow> MatchAnd (Match (Extra e1)) m2')" |
    "compress_extra (MatchAnd m1 m2) = MatchAnd (compress_extra m1) (compress_extra m2)" |
    (*"compress_extra (MatchAnd m1 m2) = (case (compress_extra m1, compress_extra m2) of 
          (Match (Extra e1), Match (Extra e2)) \<Rightarrow> Match (Extra (e1@'' ''@e2))
        | (Match (Extra e1), MatchAny) \<Rightarrow> Match (Extra e1)
        | (MatchAny, Match (Extra e2)) \<Rightarrow> Match (Extra e2)
        | (m1', m2') \<Rightarrow> MatchAnd m1' m2')" |*)
    "compress_extra MatchAny = MatchAny"
  
  thm compress_extra.simps
  
  value "compress_extra (MatchAnd (Match (Extra ''foo'')) (Match (Extra ''bar'')))"
  value "compress_extra (MatchAnd (Match (Extra ''foo'')) (MatchNot (Match (Extra ''bar''))))"
  value "compress_extra (MatchAnd (Match (Extra ''-m'')) (MatchAnd (Match (Extra ''addrtype'')) (MatchAnd (Match (Extra ''--dst-type'')) (MatchAnd (Match (Extra ''BROADCAST'')) MatchAny))))"
  
  lemma compress_extra_correct_matchexpr:
    fixes \<beta>::"('i::len common_primitive, ('i::len, 'a) tagged_packet_scheme) exact_match_tac"
    assumes generic: "primitive_matcher_generic \<beta>"
    shows "matches (\<beta>, \<alpha>) m = matches (\<beta>, \<alpha>) (compress_extra m)"
    proof(simp add: fun_eq_iff, clarify, rename_tac a p)
      fix a and p :: "('i, 'a) tagged_packet_scheme"
      from generic have "\<beta> (Extra e) p = TernaryUnknown" for e by(simp add: primitive_matcher_generic.Extra)
      hence "ternary_ternary_eval (map_match_tac \<beta> p m) = ternary_ternary_eval (map_match_tac \<beta> p (compress_extra m))"
        proof(induction m rule: compress_extra.induct)
        case 4 thus ?case
          by(simp_all split: match_expr.split match_expr.split_asm common_primitive.split)
        qed (simp_all)
      thus "matches (\<beta>, \<alpha>) m a p = matches (\<beta>, \<alpha>) (compress_extra m) a p"
        by(rule matches_iff_apply_f)
      qed

end

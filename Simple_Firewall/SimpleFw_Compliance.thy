theory SimpleFw_Compliance
imports SimpleFw_Semantics "../Primitive_Matchers/IPPortIfaceSpace_Matcher" "../Semantics_Ternary"
        "../Output_Format/Negation_Type_Matching"
        "../Bitmagic/Numberwang_Ln" (*unused?*)
        "../Bitmagic/CIDRSplit"
begin

fun ipv4_word_netmask_to_ipt_ipv4range :: "(ipv4addr \<times> nat) \<Rightarrow> ipt_ipv4range" where
  "ipv4_word_netmask_to_ipt_ipv4range (ip, n) = Ip4AddrNetmask (dotteddecimal_of_ipv4addr ip) n"

fun ipt_ipv4range_to_ipv4_word_netmask :: "ipt_ipv4range \<Rightarrow> (ipv4addr \<times> nat)" where
  "ipt_ipv4range_to_ipv4_word_netmask (Ip4Addr ip_ddecim) = (ipv4addr_of_dotteddecimal ip_ddecim, 32)" | 
  "ipt_ipv4range_to_ipv4_word_netmask (Ip4AddrNetmask pre len) = (ipv4addr_of_dotteddecimal pre, len)"
  (*we could make sure here that this is a @{term valid_prefix}, \<dots>*)

(*from ipv4range_set_from_bitmask_alt*)
(*TODO: this looks horrible! How are caesar's ranges constructed?*)

fun invert_ipv4intervall :: "(ipv4addr \<times> ipv4addr) \<Rightarrow> (ipv4addr \<times> ipv4addr) list" where
  "invert_ipv4intervall (i, j) = br2l (ipv4range_invert (ipv4range_range i j))"

lemma helper_ipv4range_range_l2br: "ipv4range_range i j = l2br [(i,j)]"
  by(simp add: ipv4range_range_def)
lemma "(l_br_toset (invert_ipv4intervall (i, j))) = - {i .. j}"
  apply(simp add: l2br_br2l ipv4range_UNIV_def ipv4range_setminus_def ipv4range_invert_def helper_ipv4range_range_l2br l_br_toset)
  by blast
  


(*do I need monads?*)
(*TODO: move*)
fun negation_type_to_match_expr :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a negation_type \<Rightarrow> 'b match_expr" where
  "negation_type_to_match_expr f (Pos a) = Match (f a)" |
  "negation_type_to_match_expr f (Neg a) = MatchNot (Match (f a))"


(*TODO: smelly duplication*)
lemma matches_SrcDst_simple_match: "p_src p \<in> ipv4s_to_set (ipv4_word_netmask_to_ipt_ipv4range ip) \<longleftrightarrow> simple_match_ip ip (p_src p)"
    "p_dst p \<in> ipv4s_to_set (ipv4_word_netmask_to_ipt_ipv4range ip) \<longleftrightarrow> simple_match_ip ip (p_dst p)"
apply(case_tac [!] ip)
apply(rename_tac b m)
by(simp_all add: bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary ipv4addr_of_dotteddecimal_dotteddecimal_of_ipv4addr)


subsection{*Simple Match to MatchExpr*}

fun simple_match_to_ipportiface_match :: "simple_match \<Rightarrow> ipportiface_rule_match match_expr" where
  "simple_match_to_ipportiface_match \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr> = 
    MatchAnd (Match (IIface iif)) (MatchAnd (Match (OIface oif)) 
    (MatchAnd (Match (Src (ipv4_word_netmask_to_ipt_ipv4range sip)))
    (MatchAnd (Match (Dst (ipv4_word_netmask_to_ipt_ipv4range dip)))
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


subsubsection{*Merging Simple Matches*}
text{*@{typ "simple_match"} @{text \<and>} @{typ "simple_match"}*}

  fun simple_match_and :: "simple_match \<Rightarrow> simple_match \<Rightarrow> simple_match option" where
    "simple_match_and \<lparr>iiface=iif1, oiface=oif1, src=sip1, dst=dip1, proto=p1, sports=sps1, dports=dps1 \<rparr> 
                      \<lparr>iiface=iif2, oiface=oif2, src=sip2, dst=dip2, proto=p2, sports=sps2, dports=dps2 \<rparr> = 
      (case simple_ips_conjunct sip1 sip2 of None \<Rightarrow> None | Some sip \<Rightarrow> 
      (case simple_ips_conjunct dip1 dip2 of None \<Rightarrow> None | Some dip \<Rightarrow> 
      (case iface_conjunct iif1 iif2 of None \<Rightarrow> None | Some iif \<Rightarrow>
      (case iface_conjunct oif1 oif2 of None \<Rightarrow> None | Some oif \<Rightarrow>
      (case simple_proto_conjunct p1 p2 of None \<Rightarrow> None | Some p \<Rightarrow>
      Some \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p,
            sports=simpl_ports_conjunct sps1 sps2, dports=simpl_ports_conjunct dps1 dps2 \<rparr>)))))"

   lemma simple_match_and_correct: "simple_matches m1 p \<and> simple_matches m2 p \<longleftrightarrow> 
    (case simple_match_and m1 m2 of None \<Rightarrow> False | Some m \<Rightarrow> simple_matches m p)"
   proof -
    obtain iif1 oif1 sip1 dip1 p1 sps1 dps1 where m1:
      "m1 = \<lparr>iiface=iif1, oiface=oif1, src=sip1, dst=dip1, proto=p1, sports=sps1, dports=dps1 \<rparr>" by(cases m1, blast)
    obtain iif2 oif2 sip2 dip2 p2 sps2 dps2 where m2:
      "m2 = \<lparr>iiface=iif2, oiface=oif2, src=sip2, dst=dip2, proto=p2, sports=sps2, dports=dps2 \<rparr>" by(cases m2, blast)

    have sip_None: "simple_ips_conjunct sip1 sip2 = None \<Longrightarrow> \<not> simple_match_ip sip1 (p_src p) \<or> \<not> simple_match_ip sip2 (p_src p)"
      using simple_match_ip_conjunct[of sip1 "p_src p" sip2] by simp
    have dip_None: "simple_ips_conjunct dip1 dip2 = None \<Longrightarrow> \<not> simple_match_ip dip1 (p_dst p) \<or> \<not> simple_match_ip dip2 (p_dst p)"
      using simple_match_ip_conjunct[of dip1 "p_dst p" dip2] by simp
    have sip_Some: "\<And>ip. simple_ips_conjunct sip1 sip2 = Some ip \<Longrightarrow>
      simple_match_ip ip (p_src p) \<longleftrightarrow> simple_match_ip sip1 (p_src p) \<and> simple_match_ip sip2 (p_src p)"
      using simple_match_ip_conjunct[of sip1 "p_src p" sip2] by simp
    have dip_Some: "\<And>ip. simple_ips_conjunct dip1 dip2 = Some ip \<Longrightarrow>
      simple_match_ip ip (p_dst p) \<longleftrightarrow> simple_match_ip dip1 (p_dst p) \<and> simple_match_ip dip2 (p_dst p)"
      using simple_match_ip_conjunct[of dip1 "p_dst p" dip2] by simp

    have iiface_None: "iface_conjunct iif1 iif2 = None \<Longrightarrow> \<not> match_iface iif1 (p_iiface p) \<or> \<not> match_iface iif2 (p_iiface p)"
      using iface_conjunct[of iif1 "(p_iiface p)" iif2] by simp
    have oiface_None: "iface_conjunct oif1 oif2 = None \<Longrightarrow> \<not> match_iface oif1 (p_oiface p) \<or> \<not> match_iface oif2 (p_oiface p)"
      using iface_conjunct[of oif1 "(p_oiface p)" oif2] by simp
    have iiface_Some: "\<And>iface. iface_conjunct iif1 iif2 = Some iface \<Longrightarrow> 
      match_iface iface (p_iiface p) \<longleftrightarrow> match_iface iif1 (p_iiface p) \<and> match_iface iif2 (p_iiface p)"
      using iface_conjunct[of iif1 "(p_iiface p)" iif2] by simp
    have oiface_Some: "\<And>iface. iface_conjunct oif1 oif2 = Some iface \<Longrightarrow> 
      match_iface iface (p_oiface p) \<longleftrightarrow> match_iface oif1 (p_oiface p) \<and> match_iface oif2 (p_oiface p)"
      using iface_conjunct[of oif1 "(p_oiface p)" oif2] by simp

    have proto_None: "simple_proto_conjunct p1 p2 = None \<Longrightarrow> \<not> match_proto p1 (p_proto p) \<or> \<not> match_proto p2 (p_proto p)"
      using simple_proto_conjunct_correct[of p1 "(p_proto p)" p2] by simp
    have proto_Some: "\<And>proto. simple_proto_conjunct p1 p2 = Some proto \<Longrightarrow>
      match_proto proto (p_proto p) \<longleftrightarrow> match_proto p1 (p_proto p) \<and> match_proto p2 (p_proto p)"
      using simple_proto_conjunct_correct[of p1 "(p_proto p)" p2] by simp

    thm simpl_ports_conjunct_correct
    show ?thesis
     apply(simp add: m1 m2)
     apply(simp split: option.split)
     apply(auto)
     apply(auto dest: sip_None dip_None sip_Some dip_Some)
     apply(auto dest: iiface_None oiface_None iiface_Some oiface_Some)
     apply(auto dest: proto_None proto_Some)
     using simpl_ports_conjunct_correct apply(blast)+
     done
   qed


fun ipportiface_match_to_simple_match :: "ipportiface_rule_match match_expr \<Rightarrow> simple_match option" where
  "ipportiface_match_to_simple_match MatchAny = Some (simple_match_any)" |
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
  "ipportiface_match_to_simple_match (MatchNot (Match (Prot ProtoAny))) = None" |
  --"TODO:"
  "ipportiface_match_to_simple_match (MatchAnd m1 m2) = (case (ipportiface_match_to_simple_match m1, ipportiface_match_to_simple_match m2) of 
      (None, _) \<Rightarrow> None
    | (_, None) \<Rightarrow> None
    | (Some m1', Some m2') \<Rightarrow> simple_match_and m1' m2')" |
  (*TODO: normalize protocols by assumption!*)
  "ipportiface_match_to_simple_match (MatchNot (Match (Prot _))) = undefined" |
  (*NOOOOO: what to do about this? Assume: no negated interfaces, I don't know of a better solution now. Just define that this must not happen*)
  "ipportiface_match_to_simple_match (MatchNot (Match (IIface iif))) = undefined (*[simple_match_any\<lparr> iiface := Iface (Neg eth) \<rparr>]*)" |
  "ipportiface_match_to_simple_match (MatchNot (Match (OIface oif))) = undefined" |
  --"undefined cases, normalize before!"
  "ipportiface_match_to_simple_match (MatchNot (Match (Src _))) = undefined" |
  "ipportiface_match_to_simple_match (MatchNot (Match (Dst _))) = undefined" |
  "ipportiface_match_to_simple_match (MatchNot (MatchAnd _ _)) = undefined" |
  "ipportiface_match_to_simple_match (MatchNot (MatchNot _)) = undefined" |
  "ipportiface_match_to_simple_match (Match (Src_Ports (_#_))) = undefined" |
  "ipportiface_match_to_simple_match (Match (Dst_Ports (_#_))) = undefined" |
  "ipportiface_match_to_simple_match (MatchNot (Match (Src_Ports _))) = undefined" |
  "ipportiface_match_to_simple_match (MatchNot (Match (Dst_Ports _))) = undefined" |
  "ipportiface_match_to_simple_match (Match (Extra _)) = undefined" |
  "ipportiface_match_to_simple_match (MatchNot (Match (Extra _))) = undefined"
(*\<dots>*)


subsubsection{*Normalizing Interfaces*}
text{*As for now, negated interfaces are simply not allowed*}

  fun normalized_ifaces :: "ipportiface_rule_match match_expr \<Rightarrow> bool" where
    "normalized_ifaces MatchAny = True" |
    "normalized_ifaces (Match _) = True" |
    "normalized_ifaces (MatchNot (Match (IIface _))) = False" |
    "normalized_ifaces (MatchNot (Match (OIface _))) = False" |
    "normalized_ifaces (MatchAnd m1 m2) = (normalized_ifaces m1 \<and> normalized_ifaces m2)" |
    "normalized_ifaces (MatchNot (MatchAnd _ _)) = False" |
    "normalized_ifaces (MatchNot _) = True" 


subsection{*Normalizing IP Addresses*}
  fun normalized_src_ips :: "ipportiface_rule_match match_expr \<Rightarrow> bool" where
    "normalized_src_ips MatchAny = True" |
    "normalized_src_ips (Match _) = True" |
    "normalized_src_ips (MatchNot (Match (Src _))) = False" |
    "normalized_src_ips (MatchAnd m1 m2) = (normalized_src_ips m1 \<and> normalized_src_ips m2)" |
    "normalized_src_ips (MatchNot (MatchAnd _ _)) = False" |
    "normalized_src_ips (MatchNot _) = True" 
  


  fun normalized_dst_ips :: "ipportiface_rule_match match_expr \<Rightarrow> bool" where
    "normalized_dst_ips MatchAny = True" |
    "normalized_dst_ips (Match _) = True" |
    "normalized_dst_ips (MatchNot (Match (Dst _))) = False" |
    "normalized_dst_ips (MatchAnd m1 m2) = (normalized_dst_ips m1 \<and> normalized_dst_ips m2)" |
    "normalized_dst_ips (MatchNot (MatchAnd _ _)) = False" |
    "normalized_dst_ips (MatchNot _) = True" 
  

  
  (*Move to motivation of CIDR split*)
  value "map (ipv4addr_of_nat \<circ> nat) [1 .. 4]"
  definition ipv4addr_upto :: "ipv4addr \<Rightarrow> ipv4addr \<Rightarrow> ipv4addr list" where
    "ipv4addr_upto i j \<equiv> map (ipv4addr_of_nat \<circ> nat) [int (nat_of_ipv4addr i) .. int (nat_of_ipv4addr j)]"
  lemma helpX:"(f \<circ> nat) ` {int i..int j} = f ` {i .. j}"
    apply(intro set_eqI)
    apply(safe)
     apply(force)
    by (metis Set_Interval.transfer_nat_int_set_functions(2) image_comp image_eqI)
  lemma ipv4addr_of_nat_def': "ipv4addr_of_nat = of_nat" using ipv4addr_of_nat_def fun_eq_iff by presburger
  lemma ipv4addr_upto: "set (ipv4addr_upto i j) = {i .. j}"
    unfolding ipv4addr_upto_def
    apply(intro set_eqI)
    apply(simp add: ipv4addr_of_nat_def' nat_of_ipv4addr_def)
    apply(safe)
    apply(simp_all)
    thm le_unat_uoi nat_mono uint_nat unat_def word_le_nat_alt
     apply (metis (no_types, hide_lams) le_unat_uoi nat_mono uint_nat unat_def word_le_nat_alt)
     apply (metis (no_types, hide_lams) le_unat_uoi nat_mono uint_nat unat_def word_le_nat_alt)
    apply(simp add: helpX)
  by (metis atLeastAtMost_iff image_eqI word_le_nat_alt word_unat.Rep_inverse)
    
  
  (*
  fun helper_construct_ip_matchexp :: "(ipv4addr \<times> ipv4addr) \<Rightarrow> ipt_ipv4range list" where
    "helper_construct_ip_matchexp (s, e) = map (Ip4Addr \<circ> dotteddecimal_of_ipv4addr) (ipv4addr_upto s e)"
  *)
  
  fun ipt_ipv4range_invert :: "ipt_ipv4range \<Rightarrow> (ipv4addr \<times> nat) list" where
    "ipt_ipv4range_invert (Ip4Addr addr) = ipv4range_split (bitrange_invert (ipv4range_single (ipv4addr_of_dotteddecimal addr)))" | 
    "ipt_ipv4range_invert (Ip4AddrNetmask base len) = ipv4range_split (bitrange_invert 
        (prefix_to_range (ipv4addr_of_dotteddecimal base AND NOT mask (32 - len), len)))"

    (*the bitmagic (pfxm_prefix pfx) AND pfxm_mask pfx). we just want to make sure to get a valid_prefix*)
    lemma cornys_hacky_call_to_prefix_to_range_to_start_with_a_valid_prefix: "valid_prefix (base AND NOT mask (32 - len), len)"
      apply(simp add: valid_prefix_def pfxm_mask_def pfxm_length_def pfxm_prefix_def)
      by (metis mask_and_not_mask_helper)
      

  (* okay, we only need to focus in the generic case *)
  lemma ipt_ipv4range_invert_case_Ip4Addr: "ipt_ipv4range_invert (Ip4Addr addr) = ipt_ipv4range_invert (Ip4AddrNetmask addr 32)"
    apply(simp add: prefix_to_range_ipv4range_range pfxm_prefix_def ipv4range_single_def)
    apply(subgoal_tac "pfxm_mask (ipv4addr_of_dotteddecimal addr, 32) = (0::ipv4addr)")
     apply(simp add: ipv4range_range_def)
    apply(simp add: pfxm_mask_def pfxm_length_def)
    done

  (*TODO: move? to caesar*)
  lemma prefix_bitrang_list_union: "\<forall> pfx \<in> set cidrlist. (valid_prefix pfx) \<Longrightarrow>
         bitrange_to_set (list_to_bitrange (map prefix_to_range cidrlist)) =
         \<Union>((\<lambda>(base, len). ipv4range_set_from_bitmask base len) ` set (cidrlist))"
         apply(induction cidrlist)
          apply(simp)
         apply(simp)
         apply(subst prefix_to_range_set_eq)
         apply(subst bitrange_to_set_ipv4range_set_from_bitmask)
          defer
          apply(simp add: pfxm_prefix_def pfxm_length_def)
          apply(clarify)
          apply(simp)
         apply(simp)
         done
  
  lemma ipt_ipv4range_invert_case_Ip4AddrNetmask:
      "(\<Union> ((\<lambda> (base, len). ipv4range_set_from_bitmask base len) ` (set (ipt_ipv4range_invert (Ip4AddrNetmask base len))) )) = 
        - (ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal base) len)"
     proof - 
      { fix r
        have "\<forall>pfx\<in>set (ipv4range_split (bitrange_invert r)). valid_prefix pfx" using all_valid_Ball by blast
        with prefix_bitrang_list_union have
        "\<Union>((\<lambda>(base, len). ipv4range_set_from_bitmask base len) ` set (ipv4range_split (bitrange_invert r))) =
        bitrange_to_set (list_to_bitrange (map prefix_to_range (ipv4range_split (bitrange_invert r))))" by simp
        also have "\<dots> = bitrange_to_set (bitrange_invert r)"
          unfolding bitrange_eq_set_eq[symmetric] using ipv4range_split_union[of "(bitrange_invert r)"] ipv4range_eq_def by simp
        also have "\<dots> = - bitrange_to_set r" by auto
        finally have "\<Union>((\<lambda>(base, len). ipv4range_set_from_bitmask base len) ` set (ipv4range_split (bitrange_invert r))) = - bitrange_to_set r" .
      } from this[of "(prefix_to_range (ipv4addr_of_dotteddecimal base  AND NOT mask (32 - len), len))"]
        show ?thesis
        apply(simp only: ipt_ipv4range_invert.simps)
        apply(simp add: prefix_to_range_set_eq)
        apply(simp add: cornys_hacky_call_to_prefix_to_range_to_start_with_a_valid_prefix pfxm_length_def pfxm_prefix_def bitrange_to_set_ipv4range_set_from_bitmask)
        apply(thin_tac "?X")
        by (metis ipv4range_set_from_bitmask_alt1 ipv4range_set_from_netmask_base_mask_consume maskshift_eq_not_mask)
     qed

  lemma ipt_ipv4range_invert: "(\<Union> ((\<lambda> (base, len). ipv4range_set_from_bitmask base len) ` (set (ipt_ipv4range_invert ips)) )) = - ipv4s_to_set ips"
    apply(cases ips)
     apply(simp_all only:)
     prefer 2
     using ipt_ipv4range_invert_case_Ip4AddrNetmask apply simp
    apply(subst ipt_ipv4range_invert_case_Ip4Addr) (* yayyy, do the same proof again *)
    apply(subst ipt_ipv4range_invert_case_Ip4AddrNetmask)
    apply(simp add: ipv4range_set_from_bitmask_32)
    done

 
  lemma "matches (ipportiface_matcher, \<alpha>) (MatchNot (Match (Src ip))) a p \<longleftrightarrow> p_src p \<in> (- (ipv4s_to_set ip))"
    using match_simplematcher_SrcDst_not by simp
  lemma match_list_match_SrcDst:
      "match_list (ipportiface_matcher, \<alpha>) (map (Match \<circ> Src) (ips::ipt_ipv4range list)) a p \<longleftrightarrow> p_src p \<in> (\<Union> (ipv4s_to_set ` (set ips)))"
      "match_list (ipportiface_matcher, \<alpha>) (map (Match \<circ> Dst) (ips::ipt_ipv4range list)) a p \<longleftrightarrow> p_dst p \<in> (\<Union> (ipv4s_to_set ` (set ips)))"
    by(simp_all add: match_list_matches IPPortIfaceSpace_Matcher.match_simplematcher_SrcDst)

  lemma match_list_ipt_ipv4range_invert:
        "match_list (ipportiface_matcher, \<alpha>) (map (Match \<circ> Src \<circ> (\<lambda>(ip, n). Ip4AddrNetmask (dotteddecimal_of_ipv4addr ip) n)) (ipt_ipv4range_invert ip)) a p \<longleftrightarrow> 
         matches (ipportiface_matcher, \<alpha>) (MatchNot (Match (Src ip))) a p" (is "?m1 = ?m2")
    proof -
      {fix ips
      have "ipv4s_to_set ` set (map (\<lambda>(ip, n). Ip4AddrNetmask (dotteddecimal_of_ipv4addr ip) n) ips) =
                   (\<lambda>(ip, n). ipv4range_set_from_bitmask ip n) ` set ips"
        apply(induction ips)
         apply(simp)
        apply(clarify)
        apply(simp add: ipv4addr_of_dotteddecimal_dotteddecimal_of_ipv4addr)
        done
      } note myheper=this[of "(ipt_ipv4range_invert ip)"]
            
      from match_list_match_SrcDst[of _ "map (\<lambda>(ip, n). Ip4AddrNetmask (dotteddecimal_of_ipv4addr ip) n) (ipt_ipv4range_invert ip)"] have
        "?m1 = (p_src p \<in> \<Union>(ipv4s_to_set ` set (map (\<lambda>(ip, n). Ip4AddrNetmask (dotteddecimal_of_ipv4addr ip) n) (ipt_ipv4range_invert ip))))" by simp
      also have "\<dots> = (p_src p \<in> \<Union>((\<lambda>(base, len). ipv4range_set_from_bitmask base len) ` set (ipt_ipv4range_invert ip)))" using myheper by presburger
      also have "\<dots> = (p_src p \<in> - ipv4s_to_set ip)" using ipt_ipv4range_invert[of ip] by simp
      also have "\<dots> = ?m2" using match_simplematcher_SrcDst_not by simp
      finally show ?thesis .
    qed
        

  (*
  fun helper_construct_ip_matchexp :: "(ipv4addr \<times> ipv4addr) \<Rightarrow> ipt_ipv4range list" where
    "helper_construct_ip_matchexp (s, e) = map (\<lambda>(ip, n). Ip4AddrNetmask (dotteddecimal_of_ipv4addr ip) n) (ipv4range_split (ipv4range_range s e))"
  declare helper_construct_ip_matchexp.simps[simp del]
    
    lemma helper_construct_ip_matchexp_set: "(\<Union> (ipv4s_to_set ` (set (helper_construct_ip_matchexp r)))) = {fst r .. snd r}"
      proof -
        have hlp1: "\<And>m. (ipv4s_to_set (case m of (ip, n) \<Rightarrow> Ip4AddrNetmask (dotteddecimal_of_ipv4addr ip) n)) = 
            (ipv4range_set_from_bitmask (fst m) (snd m))"
          by(case_tac m, simp add: ipv4addr_of_dotteddecimal_dotteddecimal_of_ipv4addr)
    
        have hlp2: "(\<Union>(ipv4s_to_set ` set (helper_construct_ip_matchexp r))) = 
               (\<Union>((\<lambda>(base, len). ipv4range_set_from_bitmask base len) ` set (ipv4range_split (ipv4range_range (fst r) (snd r)))))"
          apply(cases r, simp)
          apply(simp add: helper_construct_ip_matchexp.simps)
          apply(simp add: hlp1)
          by fastforce
        show ?thesis
          unfolding hlp2
          unfolding ipv4range_split_bitmask
          by(simp)
      qed
   *)
  (*
  lemma helper_construct_ip_matchexp_SrcDst_match_list:
    "match_list (ipportiface_matcher, \<alpha>) (map (Match \<circ> Src) (helper_construct_ip_matchexp ip)) a p \<longleftrightarrow> simple_match_ip ip (p_src p)"
    "match_list (ipportiface_matcher, \<alpha>) (map (Match \<circ> Dst) (helper_construct_ip_matchexp ip)) a p \<longleftrightarrow> simple_match_ip ip (p_dst p)"
     apply(case_tac [!] ip, rename_tac i j)
     apply(subst match_list_match_SrcDst, subst helper_construct_ip_matchexp_set, simp)+
     done
  
  hide_fact match_list_match_SrcDst helper_construct_ip_matchexp_set
  
  lemma matches_SrcDst_simple_match:
        "matches (ipportiface_matcher, \<alpha>) (match_list_to_match_expr (map (Match \<circ> Src) (helper_construct_ip_matchexp sip))) a p \<longleftrightarrow>
         simple_match_ip sip (p_src p)"
        "matches (ipportiface_matcher, \<alpha>) (match_list_to_match_expr (map (Match \<circ> Dst) (helper_construct_ip_matchexp dip))) a p \<longleftrightarrow>
         simple_match_ip dip (p_dst p)"
    apply(simp_all add: match_list_to_match_expr_disjunction helper_construct_ip_matchexp_SrcDst_match_list[where \<alpha>=\<alpha> and a=a, symmetric])
    done
  *)
  (*
  value "normalize_match (simple_match_to_ipportiface_match 
      \<lparr>iiface=Iface ''+'', oiface=Iface ''+'', src=(0,65535), dst=(0,1), proto=Proto (Pos TCP), 
        sports=(22,22), dports=(1024,65535) \<rparr>)"
  text{*when we normalize, we get at most one match expression for the size of the src ip range times size dst ip range. The CIDR range optimization is cool*}
  value "normalize_match (simple_match_to_ipportiface_match 
      \<lparr>iiface=Iface ''+'', oiface=Iface ''+'', src=(0,65535), dst=(0,1), proto=Proto (Pos TCP), 
        sports=(22,22), dports=(1024,65535) \<rparr>)"
  *)
  

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
  text{* @{typ "ipt_ports list \<Rightarrow> ipt_ports list"} *}
  definition ipt_ports_andlist_compress :: "('a::len word \<times> 'a::len word) list list \<Rightarrow> ('a::len word \<times> 'a::len word) list" where
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


end

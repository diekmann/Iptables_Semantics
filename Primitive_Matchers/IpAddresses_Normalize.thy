theory IpAddresses_Normalize
imports IPPortIfaceSpace_Matcher
        "../Bitmagic/Numberwang_Ln" (*ipv4addr_of_dotteddecimal_dotteddecimal_of_ipv4addr, we should move this lemma?*)
        "../Bitmagic/CIDRSplit"
        "Primitive_Normalization"
begin


subsection{*Normalizing IP Addresses*}
  fun normalized_src_ips :: "common_primitive match_expr \<Rightarrow> bool" where
    "normalized_src_ips MatchAny = True" |
    "normalized_src_ips (Match _) = True" |
    "normalized_src_ips (MatchNot (Match (Src _))) = False" |
    "normalized_src_ips (MatchAnd m1 m2) = (normalized_src_ips m1 \<and> normalized_src_ips m2)" |
    "normalized_src_ips (MatchNot (MatchAnd _ _)) = False" |
    "normalized_src_ips (MatchNot _) = True" 
  


  fun normalized_dst_ips :: "common_primitive match_expr \<Rightarrow> bool" where
    "normalized_dst_ips MatchAny = True" |
    "normalized_dst_ips (Match _) = True" |
    "normalized_dst_ips (MatchNot (Match (Dst _))) = False" |
    "normalized_dst_ips (MatchAnd m1 m2) = (normalized_dst_ips m1 \<and> normalized_dst_ips m2)" |
    "normalized_dst_ips (MatchNot (MatchAnd _ _)) = False" |
    "normalized_dst_ips (MatchNot _) = True" 
  

  
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

  (* okay, this is how we want to rewrite one negated ip range. need to show that result is normalized. Well, it will not be normalized, we need to split so several
     match expressions to get a normalized (non-negated) ip*)
  lemma "matches (ipportiface_matcher, \<alpha>) (match_list_to_match_expr 
            (map (Match \<circ> Src \<circ> (\<lambda>(ip, n). Ip4AddrNetmask (dotteddecimal_of_ipv4addr ip) n)) (ipt_ipv4range_invert ip))) a p \<longleftrightarrow> 
         matches (ipportiface_matcher, \<alpha>) (MatchNot (Match (Src ip))) a p"
    apply(subst match_list_ipt_ipv4range_invert[symmetric])
    apply(simp add: match_list_to_match_expr_disjunction)
    done


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
  
end

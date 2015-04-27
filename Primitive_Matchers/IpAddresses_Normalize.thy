theory IpAddresses_Normalize
imports Common_Primitive_Matcher
        "../Bitmagic/Numberwang_Ln" (*ipv4addr_of_dotdecimal_dotdecimal_of_ipv4addr, we should move this lemma?*)
        "../Bitmagic/CIDRSplit"
        "Primitive_Normalization"
begin



subsection{*Normalizing IP Addresses*}
  fun normalized_src_ips :: "common_primitive match_expr \<Rightarrow> bool" where
    "normalized_src_ips MatchAny = True" |
    "normalized_src_ips (Match _) = True" |
    "normalized_src_ips (MatchNot (Match (Src _))) = False" |
    "normalized_src_ips (MatchNot (Match _)) = True" |
    "normalized_src_ips (MatchAnd m1 m2) = (normalized_src_ips m1 \<and> normalized_src_ips m2)" |
    "normalized_src_ips (MatchNot (MatchAnd _ _)) = False" |
    "normalized_src_ips (MatchNot (MatchNot _)) = False" |
    "normalized_src_ips (MatchNot (MatchAny)) = True" 
  
  lemma normalized_src_ips_def2: "normalized_src_ips ms = normalized_n_primitive (is_Src, src_sel) (\<lambda>ip. True) ms"
    by(induction ms rule: normalized_src_ips.induct, simp_all)

  fun normalized_dst_ips :: "common_primitive match_expr \<Rightarrow> bool" where
    "normalized_dst_ips MatchAny = True" |
    "normalized_dst_ips (Match _) = True" |
    "normalized_dst_ips (MatchNot (Match (Dst _))) = False" |
    "normalized_dst_ips (MatchNot (Match _)) = True" |
    "normalized_dst_ips (MatchAnd m1 m2) = (normalized_dst_ips m1 \<and> normalized_dst_ips m2)" |
    "normalized_dst_ips (MatchNot (MatchAnd _ _)) = False" |
    "normalized_dst_ips (MatchNot (MatchNot _)) = False" |
    "normalized_dst_ips (MatchNot MatchAny) = True" 
  
  lemma normalized_dst_ips_def2: "normalized_dst_ips ms = normalized_n_primitive (is_Dst, dst_sel) (\<lambda>ip. True) ms"
    by(induction ms rule: normalized_dst_ips.induct, simp_all)
  


  definition ipt_ipv4range_negation_type_to_br_intersect :: "ipt_ipv4range negation_type list \<Rightarrow> 32 wordinterval" where
    "ipt_ipv4range_negation_type_to_br_intersect l = l2br_negation_type_intersect (NegPos_map ipt_ipv4range_to_intervall l)" 

  lemma ipt_ipv4range_negation_type_to_br_intersect: "wordinterval_to_set (ipt_ipv4range_negation_type_to_br_intersect l) =
      (\<Inter> ip \<in> set (getPos l). ipv4s_to_set ip) - (\<Union> ip \<in> set (getNeg l). ipv4s_to_set ip)"
    apply(simp add: ipt_ipv4range_negation_type_to_br_intersect_def l2br_negation_type_intersect NegPos_map_simps)
    using ipt_ipv4range_to_intervall by blast


  definition br_2_cidr_ipt_ipv4range_list :: "32 wordinterval \<Rightarrow> ipt_ipv4range list" where
    "br_2_cidr_ipt_ipv4range_list r = map (\<lambda> (base, len). Ip4AddrNetmask (dotdecimal_of_ipv4addr base) len) (ipv4range_split r)"


  lemma br_2_cidr_ipt_ipv4range_list: "(\<Union> ip \<in> set (br_2_cidr_ipt_ipv4range_list r). ipv4s_to_set ip) = wordinterval_to_set r"
    proof -
    (*have Union_rule: "\<And>P Q S. \<forall>a. P a = Q a \<Longrightarrow> (\<Union>a\<in>S. P a) = (\<Union>x\<in>S. Q x)" by presburger*)
    have "\<And>a. ipv4s_to_set (case a of (base, x) \<Rightarrow> Ip4AddrNetmask (dotdecimal_of_ipv4addr base) x) = (case a of (x, xa) \<Rightarrow> ipv4range_set_from_bitmask x xa)"
      by(clarsimp simp add: ipv4addr_of_dotdecimal_dotdecimal_of_ipv4addr)
    hence "(\<Union> ip \<in> set (br_2_cidr_ipt_ipv4range_list r). ipv4s_to_set ip) = \<Union>((\<lambda>(x, y). ipv4range_set_from_bitmask x y) ` set (ipv4range_split r))"
      unfolding br_2_cidr_ipt_ipv4range_list_def by(simp)
    thus ?thesis
    using ipv4range_split_bitmask by presburger
  qed



  definition ipt_ipv4range_compress :: "ipt_ipv4range negation_type list \<Rightarrow> ipt_ipv4range list" where
    "ipt_ipv4range_compress = br_2_cidr_ipt_ipv4range_list \<circ> ipt_ipv4range_negation_type_to_br_intersect"

  value "normalize_primitive_extract disc_sel C ipt_ipv4range_compress m"
  value "normalize_primitive_extract (is_Src, src_sel) Src ipt_ipv4range_compress (MatchAnd (MatchNot (Match (Src_Ports [(1,2)]))) (Match (Src_Ports [(1,2)])))"

  value "normalize_primitive_extract (is_Src, src_sel) Src ipt_ipv4range_compress
      (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (10,0,0,0) 2)))) (Match (Src_Ports [(1,2)])))"
  value "normalize_primitive_extract (is_Src, src_sel) Src ipt_ipv4range_compress
      (MatchAnd (Match (Src (Ip4AddrNetmask (10,0,0,0) 2))) (MatchAnd (Match (Src (Ip4AddrNetmask (10,0,0,0) 8))) (Match (Src_Ports [(1,2)]))))"
  value "normalize_primitive_extract (is_Src, src_sel) Src ipt_ipv4range_compress
      (MatchAnd (Match (Src (Ip4AddrNetmask (10,0,0,0) 2))) (MatchAnd (Match (Src (Ip4AddrNetmask (192,0,0,0) 8))) (Match (Src_Ports [(1,2)]))))"


  lemma ipt_ipv4range_compress: "(\<Union> ip \<in> set (ipt_ipv4range_compress l). ipv4s_to_set ip) =
      (\<Inter> ip \<in> set (getPos l). ipv4s_to_set ip) - (\<Union> ip \<in> set (getNeg l). ipv4s_to_set ip)"
    by (metis br_2_cidr_ipt_ipv4range_list comp_apply ipt_ipv4range_compress_def ipt_ipv4range_negation_type_to_br_intersect)
      

  definition normalize_src_ips :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr list" where
    "normalize_src_ips = normalize_primitive_extract (common_primitive.is_Src, src_sel) common_primitive.Src ipt_ipv4range_compress"
  
  lemma ipt_ipv4range_compress_src_matching: "match_list (common_matcher, \<alpha>) (map (Match \<circ> Src) (ipt_ipv4range_compress ml)) a p \<longleftrightarrow>
         matches (common_matcher, \<alpha>) (alist_and (NegPos_map Src ml)) a p"
    proof -
      have "matches (common_matcher, \<alpha>) (alist_and (NegPos_map common_primitive.Src ml)) a p \<longleftrightarrow>
            (\<forall>m \<in> set (getPos ml). matches (common_matcher, \<alpha>) (Match (Src m)) a p) \<and>
            (\<forall>m \<in> set (getNeg ml). matches (common_matcher, \<alpha>) (MatchNot (Match (Src m))) a p)"
        by(induction ml rule: alist_and.induct) (auto simp add: bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary)
      also have "\<dots> \<longleftrightarrow>  p_src p \<in>  (\<Inter> ip \<in> set (getPos ml). ipv4s_to_set ip) - (\<Union> ip \<in> set (getNeg ml). ipv4s_to_set ip)"
       by(simp add: match_simplematcher_SrcDst match_simplematcher_SrcDst_not)
      also have "\<dots> \<longleftrightarrow> p_src p \<in> (\<Union> ip \<in> set (ipt_ipv4range_compress ml). ipv4s_to_set ip)" using ipt_ipv4range_compress by presburger
      also have "\<dots> \<longleftrightarrow> (\<exists>ip \<in> set (ipt_ipv4range_compress ml). matches (common_matcher, \<alpha>) (Match (Src ip)) a p)"
       by(simp add: match_simplematcher_SrcDst)
      finally show ?thesis using match_list_matches by fastforce
  qed
  lemma normalize_src_ips: "normalized_nnf_match m \<Longrightarrow> 
      match_list (common_matcher, \<alpha>) (normalize_src_ips m) a p = matches (common_matcher, \<alpha>) m a p"
    unfolding normalize_src_ips_def
    using normalize_primitive_extract[OF _ wf_disc_sel_common_primitive(3), where f=ipt_ipv4range_compress and \<gamma>="(common_matcher, \<alpha>)"]
      ipt_ipv4range_compress_src_matching by simp

  lemma normalize_src_ips_normalized_n_primitive: "normalized_nnf_match m \<Longrightarrow> 
      \<forall>m' \<in> set (normalize_src_ips m). normalized_src_ips m'"
  unfolding normalize_src_ips_def
  unfolding normalized_src_ips_def2
  apply(rule normalize_primitive_extract_normalizes_n_primitive[OF _ wf_disc_sel_common_primitive(3)])
   by(simp_all)


  definition normalize_dst_ips :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr list" where
    "normalize_dst_ips = normalize_primitive_extract (common_primitive.is_Dst, dst_sel) common_primitive.Dst ipt_ipv4range_compress"

  lemma ipt_ipv4range_compress_dst_matching: "match_list (common_matcher, \<alpha>) (map (Match \<circ> Dst) (ipt_ipv4range_compress ml)) a p \<longleftrightarrow>
         matches (common_matcher, \<alpha>) (alist_and (NegPos_map Dst ml)) a p"
    proof -
      have "matches (common_matcher, \<alpha>) (alist_and (NegPos_map common_primitive.Dst ml)) a p \<longleftrightarrow>
            (\<forall>m \<in> set (getPos ml). matches (common_matcher, \<alpha>) (Match (Dst m)) a p) \<and>
            (\<forall>m \<in> set (getNeg ml). matches (common_matcher, \<alpha>) (MatchNot (Match (Dst m))) a p)"
        by(induction ml rule: alist_and.induct) (auto simp add: bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary)
      also have "\<dots> \<longleftrightarrow>  p_dst p \<in>  (\<Inter> ip \<in> set (getPos ml). ipv4s_to_set ip) - (\<Union> ip \<in> set (getNeg ml). ipv4s_to_set ip)"
       by(simp add: match_simplematcher_SrcDst match_simplematcher_SrcDst_not)
      also have "\<dots> \<longleftrightarrow> p_dst p \<in> (\<Union> ip \<in> set (ipt_ipv4range_compress ml). ipv4s_to_set ip)" using ipt_ipv4range_compress by presburger
      also have "\<dots> \<longleftrightarrow> (\<exists>ip \<in> set (ipt_ipv4range_compress ml). matches (common_matcher, \<alpha>) (Match (Dst ip)) a p)"
       by(simp add: match_simplematcher_SrcDst)
      finally show ?thesis using match_list_matches by fastforce
  qed
  lemma normalize_dst_ips: "normalized_nnf_match m \<Longrightarrow> 
      match_list (common_matcher, \<alpha>) (normalize_dst_ips m) a p = matches (common_matcher, \<alpha>) m a p"
    unfolding normalize_dst_ips_def
    using normalize_primitive_extract[OF _ wf_disc_sel_common_primitive(4), where f=ipt_ipv4range_compress and \<gamma>="(common_matcher, \<alpha>)"]
      ipt_ipv4range_compress_dst_matching by simp

   text{*Normalizing the dst ips preserves the normalized src ips*}
   lemma "normalized_nnf_match m \<Longrightarrow> normalized_src_ips m \<Longrightarrow> \<forall>mn\<in>set (normalize_dst_ips m). normalized_src_ips mn"
   unfolding normalize_dst_ips_def
   unfolding normalized_src_ips_def2
   apply(rule normalize_primitive_extract_preserves_unrelated_normalized_n_primitive)
   by(simp_all)



  lemma normalize_dst_ips_normalized_n_primitive: "normalized_nnf_match m \<Longrightarrow>
    \<forall>m' \<in> set (normalize_dst_ips m). normalized_dst_ips m'"
  unfolding normalize_dst_ips_def
  unfolding normalized_dst_ips_def2
  apply(rule normalize_primitive_extract_normalizes_n_primitive[OF _ wf_disc_sel_common_primitive(4)])
   by(simp_all)










(* old stuf from here: *)

subsection{*Inverting single network ranges*}
text{*unused*}
  (*
  fun helper_construct_ip_matchexp :: "(ipv4addr \<times> ipv4addr) \<Rightarrow> ipt_ipv4range list" where
    "helper_construct_ip_matchexp (s, e) = map (Ip4Addr \<circ> dotdecimal_of_ipv4addr) (ipv4addr_upto s e)"
  *)
  
  fun ipt_ipv4range_invert :: "ipt_ipv4range \<Rightarrow> (ipv4addr \<times> nat) list" where
    "ipt_ipv4range_invert (Ip4Addr addr) = ipv4range_split (wordinterval_invert (ipv4range_single (ipv4addr_of_dotdecimal addr)))" | 
    "ipt_ipv4range_invert (Ip4AddrNetmask base len) = ipv4range_split (wordinterval_invert 
        (prefix_to_range (ipv4addr_of_dotdecimal base AND NOT mask (32 - len), len)))"

    (*the bitmagic (pfxm_prefix pfx) AND pfxm_mask pfx). we just want to make sure to get a valid_prefix*)
    lemma cornys_hacky_call_to_prefix_to_range_to_start_with_a_valid_prefix: "valid_prefix (base AND NOT mask (32 - len), len)"
      apply(simp add: valid_prefix_def pfxm_mask_def pfxm_length_def pfxm_prefix_def)
      by (metis mask_and_not_mask_helper)
      

  (* okay, we only need to focus in the generic case *)
  lemma ipt_ipv4range_invert_case_Ip4Addr: "ipt_ipv4range_invert (Ip4Addr addr) = ipt_ipv4range_invert (Ip4AddrNetmask addr 32)"
    apply(simp add: prefix_to_range_ipv4range_range pfxm_prefix_def ipv4range_single_def)
    apply(subgoal_tac "pfxm_mask (ipv4addr_of_dotdecimal addr, 32) = (0::ipv4addr)")
     apply(simp add: ipv4range_range_def)
    apply(simp add: pfxm_mask_def pfxm_length_def)
    done


  
  lemma ipt_ipv4range_invert_case_Ip4AddrNetmask:
      "(\<Union> ((\<lambda> (base, len). ipv4range_set_from_bitmask base len) ` (set (ipt_ipv4range_invert (Ip4AddrNetmask base len))) )) = 
        - (ipv4range_set_from_bitmask (ipv4addr_of_dotdecimal base) len)"
     proof - 
      { fix r
        have "\<forall>pfx\<in>set (ipv4range_split (wordinterval_invert r)). valid_prefix pfx" using all_valid_Ball by blast
        with prefix_bitrang_list_union have
        "\<Union>((\<lambda>(base, len). ipv4range_set_from_bitmask base len) ` set (ipv4range_split (wordinterval_invert r))) =
        wordinterval_to_set (list_to_wordinterval (map prefix_to_range (ipv4range_split (wordinterval_invert r))))" by simp
        also have "\<dots> = wordinterval_to_set (wordinterval_invert r)"
          unfolding wordinterval_eq_set_eq[symmetric] using ipv4range_split_union[of "(wordinterval_invert r)"] ipv4range_eq_def by simp
        also have "\<dots> = - wordinterval_to_set r" by auto
        finally have "\<Union>((\<lambda>(base, len). ipv4range_set_from_bitmask base len) ` set (ipv4range_split (wordinterval_invert r))) = - wordinterval_to_set r" .
      } from this[of "(prefix_to_range (ipv4addr_of_dotdecimal base  AND NOT mask (32 - len), len))"]
        show ?thesis
        apply(simp only: ipt_ipv4range_invert.simps)
        apply(simp add: prefix_to_range_set_eq)
        apply(simp add: cornys_hacky_call_to_prefix_to_range_to_start_with_a_valid_prefix pfxm_length_def pfxm_prefix_def wordinterval_to_set_ipv4range_set_from_bitmask)
        (*apply(thin_tac "?X")*)
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

 
  lemma "matches (common_matcher, \<alpha>) (MatchNot (Match (Src ip))) a p \<longleftrightarrow> p_src p \<in> (- (ipv4s_to_set ip))"
    using match_simplematcher_SrcDst_not by simp
  lemma match_list_match_SrcDst:
      "match_list (common_matcher, \<alpha>) (map (Match \<circ> Src) (ips::ipt_ipv4range list)) a p \<longleftrightarrow> p_src p \<in> (\<Union> (ipv4s_to_set ` (set ips)))"
      "match_list (common_matcher, \<alpha>) (map (Match \<circ> Dst) (ips::ipt_ipv4range list)) a p \<longleftrightarrow> p_dst p \<in> (\<Union> (ipv4s_to_set ` (set ips)))"
    by(simp_all add: match_list_matches match_simplematcher_SrcDst)

  lemma match_list_ipt_ipv4range_invert:
        "match_list (common_matcher, \<alpha>) (map (Match \<circ> Src \<circ> (\<lambda>(ip, n). Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) n)) (ipt_ipv4range_invert ip)) a p \<longleftrightarrow> 
         matches (common_matcher, \<alpha>) (MatchNot (Match (Src ip))) a p" (is "?m1 = ?m2")
    proof -
      {fix ips
      have "ipv4s_to_set ` set (map (\<lambda>(ip, n). Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) n) ips) =
                   (\<lambda>(ip, n). ipv4range_set_from_bitmask ip n) ` set ips"
        apply(induction ips)
         apply(simp)
        apply(clarify)
        apply(simp add: ipv4addr_of_dotdecimal_dotdecimal_of_ipv4addr)
        done
      } note myheper=this[of "(ipt_ipv4range_invert ip)"]
            
      from match_list_match_SrcDst[of _ "map (\<lambda>(ip, n). Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) n) (ipt_ipv4range_invert ip)"] have
        "?m1 = (p_src p \<in> \<Union>(ipv4s_to_set ` set (map (\<lambda>(ip, n). Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) n) (ipt_ipv4range_invert ip))))" by simp
      also have "\<dots> = (p_src p \<in> \<Union>((\<lambda>(base, len). ipv4range_set_from_bitmask base len) ` set (ipt_ipv4range_invert ip)))" using myheper by presburger
      also have "\<dots> = (p_src p \<in> - ipv4s_to_set ip)" using ipt_ipv4range_invert[of ip] by simp
      also have "\<dots> = ?m2" using match_simplematcher_SrcDst_not by simp
      finally show ?thesis .
    qed

  (* okay, this is how we want to rewrite one negated ip range. need to show that result is normalized. Well, it will not be normalized, we need to split so several
     match expressions to get a normalized (non-negated) ip*)
  lemma "matches (common_matcher, \<alpha>) (match_list_to_match_expr 
            (map (Match \<circ> Src \<circ> (\<lambda>(ip, n). Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) n)) (ipt_ipv4range_invert ip))) a p \<longleftrightarrow> 
         matches (common_matcher, \<alpha>) (MatchNot (Match (Src ip))) a p"
    apply(subst match_list_ipt_ipv4range_invert[symmetric])
    apply(simp add: match_list_to_match_expr_disjunction)
    done


  (*
  fun helper_construct_ip_matchexp :: "(ipv4addr \<times> ipv4addr) \<Rightarrow> ipt_ipv4range list" where
    "helper_construct_ip_matchexp (s, e) = map (\<lambda>(ip, n). Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) n) (ipv4range_split (ipv4range_range s e))"
  declare helper_construct_ip_matchexp.simps[simp del]
    
    lemma helper_construct_ip_matchexp_set: "(\<Union> (ipv4s_to_set ` (set (helper_construct_ip_matchexp r)))) = {fst r .. snd r}"
      proof -
        have hlp1: "\<And>m. (ipv4s_to_set (case m of (ip, n) \<Rightarrow> Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) n)) = 
            (ipv4range_set_from_bitmask (fst m) (snd m))"
          by(case_tac m, simp add: ipv4addr_of_dotdecimal_dotdecimal_of_ipv4addr)
    
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
    "match_list (common_matcher, \<alpha>) (map (Match \<circ> Src) (helper_construct_ip_matchexp ip)) a p \<longleftrightarrow> simple_match_ip ip (p_src p)"
    "match_list (common_matcher, \<alpha>) (map (Match \<circ> Dst) (helper_construct_ip_matchexp ip)) a p \<longleftrightarrow> simple_match_ip ip (p_dst p)"
     apply(case_tac [!] ip, rename_tac i j)
     apply(subst match_list_match_SrcDst, subst helper_construct_ip_matchexp_set, simp)+
     done
  
  hide_fact match_list_match_SrcDst helper_construct_ip_matchexp_set
  
  lemma matches_SrcDst_simple_match:
        "matches (common_matcher, \<alpha>) (match_list_to_match_expr (map (Match \<circ> Src) (helper_construct_ip_matchexp sip))) a p \<longleftrightarrow>
         simple_match_ip sip (p_src p)"
        "matches (common_matcher, \<alpha>) (match_list_to_match_expr (map (Match \<circ> Dst) (helper_construct_ip_matchexp dip))) a p \<longleftrightarrow>
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

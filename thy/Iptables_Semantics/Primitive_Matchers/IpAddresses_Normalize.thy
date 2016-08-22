theory IpAddresses_Normalize
imports Common_Primitive_Lemmas
begin


subsection\<open>Normalizing IP Addresses\<close>
  fun normalized_src_ips :: "'i::len common_primitive match_expr \<Rightarrow> bool" where
    "normalized_src_ips MatchAny = True" |
    "normalized_src_ips (Match (Src (IpAddrRange _ _))) = False" |
    "normalized_src_ips (Match (Src (IpAddr _))) = False" |
    "normalized_src_ips (Match (Src (IpAddrNetmask _ _))) = True" |
    "normalized_src_ips (Match _) = True" |
    "normalized_src_ips (MatchNot (Match (Src _))) = False" |
    "normalized_src_ips (MatchNot (Match _)) = True" |
    "normalized_src_ips (MatchAnd m1 m2) = (normalized_src_ips m1 \<and> normalized_src_ips m2)" |
    "normalized_src_ips (MatchNot (MatchAnd _ _)) = False" |
    "normalized_src_ips (MatchNot (MatchNot _)) = False" |
    "normalized_src_ips (MatchNot (MatchAny)) = True" 
  
  lemma normalized_src_ips_def2: "normalized_src_ips ms = normalized_n_primitive (is_Src, src_sel) normalized_cidr_ip ms"
    by(induction ms rule: normalized_src_ips.induct, simp_all add: normalized_cidr_ip_def)

  fun normalized_dst_ips :: "'i::len common_primitive match_expr \<Rightarrow> bool" where
    "normalized_dst_ips MatchAny = True" |
    "normalized_dst_ips (Match (Dst (IpAddrRange _ _))) = False" |
    "normalized_dst_ips (Match (Dst (IpAddr _))) = False" |
    "normalized_dst_ips (Match (Dst (IpAddrNetmask _ _))) = True" |
    "normalized_dst_ips (Match _) = True" |
    "normalized_dst_ips (MatchNot (Match (Dst _))) = False" |
    "normalized_dst_ips (MatchNot (Match _)) = True" |
    "normalized_dst_ips (MatchAnd m1 m2) = (normalized_dst_ips m1 \<and> normalized_dst_ips m2)" |
    "normalized_dst_ips (MatchNot (MatchAnd _ _)) = False" |
    "normalized_dst_ips (MatchNot (MatchNot _)) = False" |
    "normalized_dst_ips (MatchNot MatchAny) = True" 
  
  lemma normalized_dst_ips_def2: "normalized_dst_ips ms = normalized_n_primitive (is_Dst, dst_sel) normalized_cidr_ip ms"
    by(induction ms rule: normalized_dst_ips.induct, simp_all add: normalized_cidr_ip_def)
  

  (*possible optimizations: remove the UNIV match on ip here!*)
  value "normalize_primitive_extract (is_Src, src_sel) Src ipt_iprange_compress
      (MatchAnd (MatchNot (Match ((Src_Ports (L4Ports TCP [(1,2)])):: 32 common_primitive))) (Match (Src_Ports (L4Ports TCP [(1,2)]))))"
  value "normalize_primitive_extract (is_Src, src_sel) Src ipt_iprange_compress
      (MatchAnd (MatchNot (Match (Src (IpAddrNetmask (10::ipv4addr) 2)))) (Match (Src_Ports (L4Ports TCP [(1,2)]))))"
  value "normalize_primitive_extract (is_Src, src_sel) Src ipt_iprange_compress
      (MatchAnd (Match (Src (IpAddrNetmask (10::ipv4addr) 2))) (MatchAnd (Match (Src (IpAddrNetmask 10 8))) (Match (Src_Ports (L4Ports TCP [(1,2)])))))"
  (*too many MatchAny*)
  value "normalize_primitive_extract (is_Src, src_sel) Src ipt_iprange_compress
      (MatchAnd (Match (Src (IpAddrNetmask (10::ipv4addr) 2))) (MatchAnd (Match (Src (IpAddrNetmask 192 8))) (Match (Src_Ports (L4Ports TCP [(1,2)])))))"


  definition normalize_src_ips :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr list" where
    "normalize_src_ips = normalize_primitive_extract (common_primitive.is_Src, src_sel)
                                      common_primitive.Src ipt_iprange_compress"
  
  lemma ipt_iprange_compress_src_matching: "match_list (common_matcher, \<alpha>) (map (Match \<circ> Src) (ipt_iprange_compress ml)) a p \<longleftrightarrow>
         matches (common_matcher, \<alpha>) (alist_and (NegPos_map Src ml)) a p"
    proof -
      have "matches (common_matcher, \<alpha>) (alist_and (NegPos_map common_primitive.Src ml)) a p \<longleftrightarrow>
            (\<forall>m \<in> set (getPos ml). matches (common_matcher, \<alpha>) (Match (Src m)) a p) \<and>
            (\<forall>m \<in> set (getNeg ml). matches (common_matcher, \<alpha>) (MatchNot (Match (Src m))) a p)"
        by(induction ml rule: alist_and.induct) (auto simp add: bunch_of_lemmata_about_matches)
      also have "\<dots> \<longleftrightarrow>  p_src p \<in>  (\<Inter> ip \<in> set (getPos ml). ipt_iprange_to_set ip) - (\<Union> ip \<in> set (getNeg ml). ipt_iprange_to_set ip)"
       by(simp add: match_simplematcher_SrcDst match_simplematcher_SrcDst_not)
      also have "\<dots> \<longleftrightarrow> p_src p \<in> (\<Union> ip \<in> set (ipt_iprange_compress ml). ipt_iprange_to_set ip)" using ipt_iprange_compress
        by blast
      also have "\<dots> \<longleftrightarrow> (\<exists>ip \<in> set (ipt_iprange_compress ml). matches (common_matcher, \<alpha>) (Match (Src ip)) a p)"
       by(simp add: match_simplematcher_SrcDst)
      finally show ?thesis using match_list_matches by fastforce
  qed
  lemma normalize_src_ips: "normalized_nnf_match m \<Longrightarrow> 
      match_list (common_matcher, \<alpha>) (normalize_src_ips m) a p = matches (common_matcher, \<alpha>) m a p"
    unfolding normalize_src_ips_def
    using normalize_primitive_extract[OF _ wf_disc_sel_common_primitive(3), where f=ipt_iprange_compress and \<gamma>="(common_matcher, \<alpha>)"]
      ipt_iprange_compress_src_matching by blast

  lemma normalize_src_ips_normalized_n_primitive: "normalized_nnf_match m \<Longrightarrow> 
      \<forall>m' \<in> set (normalize_src_ips m). normalized_src_ips m'"
  unfolding normalize_src_ips_def
  unfolding normalized_src_ips_def2
  apply(rule normalize_primitive_extract_normalizes_n_primitive[OF _ wf_disc_sel_common_primitive(3)])
   by(simp_all add: ipt_iprange_compress_normalized_IpAddrNetmask)


  definition normalize_dst_ips :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr list" where
    "normalize_dst_ips = normalize_primitive_extract (common_primitive.is_Dst, dst_sel)
                                common_primitive.Dst ipt_iprange_compress"

  lemma ipt_iprange_compress_dst_matching: "match_list (common_matcher, \<alpha>) (map (Match \<circ> Dst) (ipt_iprange_compress ml)) a p \<longleftrightarrow>
         matches (common_matcher, \<alpha>) (alist_and (NegPos_map Dst ml)) a p"
    proof -
      have "matches (common_matcher, \<alpha>) (alist_and (NegPos_map common_primitive.Dst ml)) a p \<longleftrightarrow>
            (\<forall>m \<in> set (getPos ml). matches (common_matcher, \<alpha>) (Match (Dst m)) a p) \<and>
            (\<forall>m \<in> set (getNeg ml). matches (common_matcher, \<alpha>) (MatchNot (Match (Dst m))) a p)"
        by(induction ml rule: alist_and.induct) (auto simp add: bunch_of_lemmata_about_matches)
      also have "\<dots> \<longleftrightarrow>  p_dst p \<in>  (\<Inter> ip \<in> set (getPos ml). ipt_iprange_to_set ip) - (\<Union> ip \<in> set (getNeg ml). ipt_iprange_to_set ip)"
       by(simp add: match_simplematcher_SrcDst match_simplematcher_SrcDst_not)
      also have "\<dots> \<longleftrightarrow> p_dst p \<in> (\<Union> ip \<in> set (ipt_iprange_compress ml). ipt_iprange_to_set ip)" using ipt_iprange_compress by blast
      also have "\<dots> \<longleftrightarrow> (\<exists>ip \<in> set (ipt_iprange_compress ml). matches (common_matcher, \<alpha>) (Match (Dst ip)) a p)"
       by(simp add: match_simplematcher_SrcDst)
      finally show ?thesis using match_list_matches by fastforce
  qed
  lemma normalize_dst_ips: "normalized_nnf_match m \<Longrightarrow> 
      match_list (common_matcher, \<alpha>) (normalize_dst_ips m) a p = matches (common_matcher, \<alpha>) m a p"
    unfolding normalize_dst_ips_def
    using normalize_primitive_extract[OF _ wf_disc_sel_common_primitive(4), where f=ipt_iprange_compress and \<gamma>="(common_matcher, \<alpha>)"]
      ipt_iprange_compress_dst_matching by blast

   text\<open>Normalizing the dst ips preserves the normalized src ips\<close>
   lemma "normalized_nnf_match m \<Longrightarrow> normalized_src_ips m \<Longrightarrow> \<forall>mn\<in>set (normalize_dst_ips m). normalized_src_ips mn"
   unfolding normalize_dst_ips_def normalized_src_ips_def2
   by(rule normalize_primitive_extract_preserves_unrelated_normalized_n_primitive)(simp_all add: wf_disc_sel_common_primitive)



  lemma normalize_dst_ips_normalized_n_primitive: "normalized_nnf_match m \<Longrightarrow>
    \<forall>m' \<in> set (normalize_dst_ips m). normalized_dst_ips m'"
  unfolding normalize_dst_ips_def normalized_dst_ips_def2
  by(rule normalize_primitive_extract_normalizes_n_primitive[OF _ wf_disc_sel_common_primitive(4)]) (simp_all add: ipt_iprange_compress_normalized_IpAddrNetmask)

end

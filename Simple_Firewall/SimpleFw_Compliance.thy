theory SimpleFw_Compliance
imports SimpleFw_Semantics "../Primitive_Matchers/Transform"
begin

fun ipv4_word_netmask_to_ipt_ipv4range :: "(ipv4addr \<times> nat) \<Rightarrow> ipt_ipv4range" where
  "ipv4_word_netmask_to_ipt_ipv4range (ip, n) = Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) n"

fun ipt_ipv4range_to_ipv4_word_netmask :: "ipt_ipv4range \<Rightarrow> (ipv4addr \<times> nat)" where
  "ipt_ipv4range_to_ipv4_word_netmask (Ip4Addr ip_ddecim) = (ipv4addr_of_dotdecimal ip_ddecim, 32)" | 
  "ipt_ipv4range_to_ipv4_word_netmask (Ip4AddrNetmask pre len) = (ipv4addr_of_dotdecimal pre, len)"
  (*we could make sure here that this is a @{term valid_prefix}, \<dots>*)



subsection{*Simple Match to MatchExpr*}

fun simple_match_to_ipportiface_match :: "simple_match \<Rightarrow> common_primitive match_expr" where
  "simple_match_to_ipportiface_match \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr> = 
    MatchAnd (Match (IIface iif)) (MatchAnd (Match (OIface oif)) 
    (MatchAnd (Match (Src (ipv4_word_netmask_to_ipt_ipv4range sip)))
    (MatchAnd (Match (Dst (ipv4_word_netmask_to_ipt_ipv4range dip)))
    (MatchAnd (Match (Prot p))
    (MatchAnd (Match (Src_Ports [sps]))
    (Match (Dst_Ports [dps]))
    )))))"


(*is this usefull?*)
lemma "matches \<gamma> (simple_match_to_ipportiface_match \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr>) a p \<longleftrightarrow> 
      matches \<gamma> (alist_and ([Pos (IIface iif), Pos (OIface oif)] @ [Pos (Src (ipv4_word_netmask_to_ipt_ipv4range sip))]
        @ [Pos (Dst (ipv4_word_netmask_to_ipt_ipv4range dip))] @ [Pos (Prot p)]
        @ [Pos (Src_Ports [sps])] @ [Pos (Dst_Ports [dps])])) a p"
apply(cases sip,cases dip)
apply(simp add: bunch_of_lemmata_about_matches)
done


lemma ports_to_set_singleton_simple_match_port: "p \<in> ports_to_set [a] \<longleftrightarrow> simple_match_port a p"
  by(cases a, simp)

theorem simple_match_to_ipportiface_match_correct: "matches (common_matcher, \<alpha>) (simple_match_to_ipportiface_match sm) a p \<longleftrightarrow> simple_matches sm p"
  proof -
  obtain iif oif sip dip pro sps dps where sm: "sm = \<lparr>iiface = iif, oiface = oif, src = sip, dst = dip, proto = pro, sports = sps, dports = dps\<rparr>" by (cases sm)
  { fix ip
    have "p_src p \<in> ipv4s_to_set (ipv4_word_netmask_to_ipt_ipv4range ip) \<longleftrightarrow> simple_match_ip ip (p_src p)"
    and  "p_dst p \<in> ipv4s_to_set (ipv4_word_netmask_to_ipt_ipv4range ip) \<longleftrightarrow> simple_match_ip ip (p_dst p)"
     apply(case_tac [!]  ip)
     by(simp_all add: bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary ipv4addr_of_dotdecimal_dotdecimal_of_ipv4addr)
  } note simple_match_ips=this
  { fix ps
    have "p_sport p \<in> ports_to_set [ps] \<longleftrightarrow> simple_match_port ps (p_sport p)"
    and  "p_dport p \<in> ports_to_set [ps] \<longleftrightarrow> simple_match_port ps (p_dport p)"
      apply(case_tac [!] ps)
      by(simp_all)
  } note simple_match_ports=this
  show ?thesis unfolding sm
  by(simp add: bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary simple_match_ips simple_match_ports simple_matches.simps)
qed


subsection{*MatchExpr to Simple Match*}


subsubsection{*Merging Simple Matches*}
text{*@{typ "simple_match"} @{text \<and>} @{typ "simple_match"}*}

  fun simple_match_and :: "simple_match \<Rightarrow> simple_match \<Rightarrow> simple_match option" where
    "simple_match_and \<lparr>iiface=iif1, oiface=oif1, src=sip1, dst=dip1, proto=p1, sports=sps1, dports=dps1 \<rparr> 
                      \<lparr>iiface=iif2, oiface=oif2, src=sip2, dst=dip2, proto=p2, sports=sps2, dports=dps2 \<rparr> = 
      (case ipv4cidr_conjunct sip1 sip2 of None \<Rightarrow> None | Some sip \<Rightarrow> 
      (case ipv4cidr_conjunct dip1 dip2 of None \<Rightarrow> None | Some dip \<Rightarrow> 
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

    have sip_None: "ipv4cidr_conjunct sip1 sip2 = None \<Longrightarrow> \<not> simple_match_ip sip1 (p_src p) \<or> \<not> simple_match_ip sip2 (p_src p)"
      using simple_match_ip_conjunct[of sip1 "p_src p" sip2] by simp
    have dip_None: "ipv4cidr_conjunct dip1 dip2 = None \<Longrightarrow> \<not> simple_match_ip dip1 (p_dst p) \<or> \<not> simple_match_ip dip2 (p_dst p)"
      using simple_match_ip_conjunct[of dip1 "p_dst p" dip2] by simp
    have sip_Some: "\<And>ip. ipv4cidr_conjunct sip1 sip2 = Some ip \<Longrightarrow>
      simple_match_ip ip (p_src p) \<longleftrightarrow> simple_match_ip sip1 (p_src p) \<and> simple_match_ip sip2 (p_src p)"
      using simple_match_ip_conjunct[of sip1 "p_src p" sip2] by simp
    have dip_Some: "\<And>ip. ipv4cidr_conjunct dip1 dip2 = Some ip \<Longrightarrow>
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

    show ?thesis
     apply(simp add: m1 m2)
     apply(simp split: option.split)
     apply(auto simp add: simple_matches.simps)
     apply(auto dest: sip_None dip_None sip_Some dip_Some)
     apply(auto dest: iiface_None oiface_None iiface_Some oiface_Some)
     apply(auto dest: proto_None proto_Some)
     using simpl_ports_conjunct_correct apply(blast)+
     done
   qed


fun common_primitive_match_to_simple_match :: "common_primitive match_expr \<Rightarrow> simple_match option" where
  "common_primitive_match_to_simple_match MatchAny = Some (simple_match_any)" |
  "common_primitive_match_to_simple_match (MatchNot MatchAny) = None" |
  "common_primitive_match_to_simple_match (Match (IIface iif)) = Some (simple_match_any\<lparr> iiface := iif \<rparr>)" |
  "common_primitive_match_to_simple_match (Match (OIface oif)) = Some (simple_match_any\<lparr> oiface := oif \<rparr>)" |
  "common_primitive_match_to_simple_match (Match (Src ip)) = Some (simple_match_any\<lparr> src := (ipt_ipv4range_to_ipv4_word_netmask ip) \<rparr>)" |
  "common_primitive_match_to_simple_match (Match (Dst ip)) = Some (simple_match_any\<lparr> dst := (ipt_ipv4range_to_ipv4_word_netmask ip) \<rparr>)" |
  "common_primitive_match_to_simple_match (Match (Prot p)) = Some (simple_match_any\<lparr> proto := p \<rparr>)" |
  "common_primitive_match_to_simple_match (Match (Src_Ports [])) = None" |
  "common_primitive_match_to_simple_match (Match (Src_Ports [(s,e)])) = Some (simple_match_any\<lparr> sports := (s,e) \<rparr>)" |
  "common_primitive_match_to_simple_match (Match (Dst_Ports [])) = None" |
  "common_primitive_match_to_simple_match (Match (Dst_Ports [(s,e)])) = Some (simple_match_any\<lparr> dports := (s,e) \<rparr>)" |
  "common_primitive_match_to_simple_match (MatchNot (Match (Prot ProtoAny))) = None" |
  "common_primitive_match_to_simple_match (MatchAnd m1 m2) = (case (common_primitive_match_to_simple_match m1, common_primitive_match_to_simple_match m2) of 
      (None, _) \<Rightarrow> None
    | (_, None) \<Rightarrow> None
    | (Some m1', Some m2') \<Rightarrow> simple_match_and m1' m2')" |
  --"undefined cases, normalize before!"
  "common_primitive_match_to_simple_match (MatchNot (Match (Prot _))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (IIface iif))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (OIface oif))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (Src _))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (Dst _))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (MatchAnd _ _)) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (MatchNot _)) = undefined" |
  "common_primitive_match_to_simple_match (Match (Src_Ports (_#_))) = undefined" |
  "common_primitive_match_to_simple_match (Match (Dst_Ports (_#_))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (Src_Ports _))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (Dst_Ports _))) = undefined" |
  "common_primitive_match_to_simple_match (Match (Extra _)) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (Extra _))) = undefined"
(*\<dots>*)



subsubsection{*Normalizing Interfaces*}
text{*As for now, negated interfaces are simply not allowed*}
  fun normalized_ifaces :: "common_primitive match_expr \<Rightarrow> bool" where
    "normalized_ifaces MatchAny = True" |
    "normalized_ifaces (Match _) = True" |
    "normalized_ifaces (MatchNot (Match (IIface _))) = False" |
    "normalized_ifaces (MatchNot (Match (OIface _))) = False" |
    "normalized_ifaces (MatchAnd m1 m2) = (normalized_ifaces m1 \<and> normalized_ifaces m2)" |
    "normalized_ifaces (MatchNot (MatchAnd _ _)) = False" |
    "normalized_ifaces (MatchNot _) = True" 


subsubsection{*Normalizing Protocols*}
text{*As for now, negated protocols are simply not allowed*}
  fun normalized_protocols :: "common_primitive match_expr \<Rightarrow> bool" where
    "normalized_protocols MatchAny = True" |
    "normalized_protocols (Match _) = True" |
    "normalized_protocols (MatchNot (Match (Prot _))) = False" |
    "normalized_protocols (MatchAnd m1 m2) = (normalized_protocols m1 \<and> normalized_protocols m2)" |
    "normalized_protocols (MatchNot (MatchAnd _ _)) = False" |
    "normalized_protocols (MatchNot _) = True" 



lemma match_iface_simple_match_any_simps:
     "match_iface (iiface simple_match_any) (p_iiface p)"
     "match_iface (oiface simple_match_any) (p_oiface p)"
     "simple_match_ip (src simple_match_any) (p_src p)"
     "simple_match_ip (dst simple_match_any) (p_dst p)"
     "match_proto (proto simple_match_any) (p_proto p)"
     "simple_match_port (sports simple_match_any) (p_sport p)"
     "simple_match_port (dports simple_match_any) (p_dport p)"
  apply(simp_all add: simple_match_any_def match_ifaceAny ipv4range_set_from_bitmask_0)
  apply(subgoal_tac [!] "(65535::16 word) = max_word")
    apply(simp_all)
  apply(simp_all add: max_word_def)
  done

theorem common_primitive_match_to_simple_match:
  assumes "normalized_src_ports m" 
      and "normalized_dst_ports m"
      and "normalized_src_ips m"
      and "normalized_dst_ips m"
      and "normalized_ifaces m"
      and "normalized_protocols m"
      and "\<not> has_disc is_Extra m"
  shows "(Some sm = common_primitive_match_to_simple_match m \<longrightarrow> matches (common_matcher, \<alpha>) m a p \<longleftrightarrow> simple_matches sm p) \<and>
         (common_primitive_match_to_simple_match m = None \<longrightarrow> \<not> matches (common_matcher, \<alpha>) m a p)"
proof -
  { fix ip
    have "p_src p \<in> ipv4s_to_set ip \<longleftrightarrow> simple_match_ip (ipt_ipv4range_to_ipv4_word_netmask ip) (p_src p)"
    and  "p_dst p \<in> ipv4s_to_set ip \<longleftrightarrow> simple_match_ip (ipt_ipv4range_to_ipv4_word_netmask ip) (p_dst p)"
    by(case_tac [!] ip)(simp_all add: ipv4range_set_from_bitmask_32)
  } note matches_SrcDst_simple_match2=this
  show ?thesis
  using assms proof(induction m arbitrary: sm rule: common_primitive_match_to_simple_match.induct)
  case 1 thus ?case 
    by(simp_all add: match_iface_simple_match_any_simps bunch_of_lemmata_about_matches(2) simple_matches.simps)
  next
  case (13 m1 m2)
    let ?caseSome="Some sm = common_primitive_match_to_simple_match (MatchAnd m1 m2)"
    let ?caseNone="common_primitive_match_to_simple_match (MatchAnd m1 m2) = None"
    let ?goal="(?caseSome \<longrightarrow> matches (common_matcher, \<alpha>) (MatchAnd m1 m2) a p = simple_matches sm p) \<and> 
               (?caseNone \<longrightarrow> \<not> matches (common_matcher, \<alpha>) (MatchAnd m1 m2) a p)"

    {  assume caseNone: ?caseNone
      { fix sm1 sm2
        assume sm1: "common_primitive_match_to_simple_match m1 = Some sm1"
           and sm2: "common_primitive_match_to_simple_match m2 = Some sm2"
           and sma: "simple_match_and sm1 sm2 = None"
        from sma simple_match_and_correct have 1: "\<not> (simple_matches sm1 p \<and> simple_matches sm2 p)" by simp
        from sm1 sm2 13 have 2: "(matches (common_matcher, \<alpha>) m1 a p \<longleftrightarrow> simple_matches sm1 p) \<and> 
                              (matches (common_matcher, \<alpha>) m2 a p \<longleftrightarrow> simple_matches sm2 p)" by force
        hence 2: "matches (common_matcher, \<alpha>) (MatchAnd m1 m2) a p \<longleftrightarrow> simple_matches sm1 p \<and> simple_matches sm2 p"
          by(simp add: bunch_of_lemmata_about_matches)
        from 1 2 have "\<not> matches (common_matcher, \<alpha>) (MatchAnd m1 m2) a p" by blast 
      }
      with caseNone have "common_primitive_match_to_simple_match m1 = None \<or>
                          common_primitive_match_to_simple_match m2 = None \<or>
                          \<not> matches (common_matcher, \<alpha>) (MatchAnd m1 m2) a p"
        by(simp split:option.split_asm)
      hence "\<not> matches (common_matcher, \<alpha>) (MatchAnd m1 m2) a p" 
        apply(elim disjE)
          apply(simp_all)
         using 13 apply(simp_all add: bunch_of_lemmata_about_matches(1))
        done
    }note caseNone=this

    { assume caseSome: ?caseSome
      hence "\<exists> sm1. common_primitive_match_to_simple_match m1 = Some sm1" and
            "\<exists> sm2. common_primitive_match_to_simple_match m2 = Some sm2"
        by(simp_all split: option.split_asm)
      from this obtain sm1 sm2 where sm1: "Some sm1 = common_primitive_match_to_simple_match m1"
                                 and sm2: "Some sm2 = common_primitive_match_to_simple_match m2" by fastforce+
      with 13 have "matches (common_matcher, \<alpha>) m1 a p = simple_matches sm1 p \<and>
                    matches (common_matcher, \<alpha>) m2 a p = simple_matches sm2 p" by simp
      hence 1: "matches (common_matcher, \<alpha>) (MatchAnd m1 m2) a p \<longleftrightarrow> simple_matches sm1 p \<and> simple_matches sm2 p"
        by(simp add: bunch_of_lemmata_about_matches)
      from caseSome sm1 sm2 have "simple_match_and sm1 sm2 = Some sm" by(simp split: option.split_asm)
      with simple_match_and_correct have 2: "simple_matches sm p \<longleftrightarrow> simple_matches sm1 p \<and> simple_matches sm2 p" by simp
      from 1 2 have "matches (common_matcher, \<alpha>) (MatchAnd m1 m2) a p = simple_matches sm p" by simp
    } note caseSome=this

    from caseNone caseSome show ?goal by blast
  qed(simp_all add: match_iface_simple_match_any_simps simple_matches.simps, 
    simp_all add: bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary matches_SrcDst_simple_match2)
qed



fun action_to_simple_action :: "action \<Rightarrow> simple_action" where
  "action_to_simple_action action.Accept = simple_action.Accept" |
  "action_to_simple_action action.Drop   = simple_action.Drop" |
  "action_to_simple_action _ = undefined"

definition check_simple_fw_preconditions :: "common_primitive rule list \<Rightarrow> bool" where
  "check_simple_fw_preconditions rs \<equiv> \<forall>r \<in> set rs. (case r of (Rule m a) \<Rightarrow> normalized_src_ports m \<and> normalized_dst_ports m \<and> normalized_src_ips m \<and> normalized_dst_ips m \<and> normalized_ifaces m \<and> 
  normalized_protocols m \<and> \<not> has_disc is_Extra m \<and> (a = action.Accept \<or> a = action.Drop))"

definition to_simple_firewall :: "common_primitive rule list \<Rightarrow> simple_rule list" where
  "to_simple_firewall rs \<equiv> if check_simple_fw_preconditions rs then
      List.map_filter (\<lambda>r. case r of Rule m a \<Rightarrow> 
        (case (common_primitive_match_to_simple_match m) of None \<Rightarrow> None |
                    Some sm \<Rightarrow> Some (SimpleRule sm (action_to_simple_action a)))) rs
    else undefined"

lemma to_simple_firewall_simps:
      "to_simple_firewall [] = []"
      "check_simple_fw_preconditions ((Rule m a)#rs) \<Longrightarrow> to_simple_firewall ((Rule m a)#rs) = (case common_primitive_match_to_simple_match m of
          None \<Rightarrow> to_simple_firewall rs
          | Some sm \<Rightarrow> (SimpleRule sm (action_to_simple_action a)) # to_simple_firewall rs)"
      "\<not> check_simple_fw_preconditions rs' \<Longrightarrow> to_simple_firewall rs' = undefined"
   by(auto simp add: to_simple_firewall_def List.map_filter_simps check_simple_fw_preconditions_def split: option.split)


value "check_simple_fw_preconditions
     [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8)))
                          (MatchAnd (Match (Dst_Ports [(0, 65535)]))
                                    (Match (Src_Ports [(0, 65535)]))))
                Drop]"
value "to_simple_firewall
     [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8)))
                          (MatchAnd (Match (Dst_Ports [(0, 65535)]))
                                    (Match (Src_Ports [(0, 65535)]))))
                Drop]"
value "check_simple_fw_preconditions [Rule (MatchAnd MatchAny MatchAny) Drop]"
value "to_simple_firewall [Rule (MatchAnd MatchAny MatchAny) Drop]"
value "to_simple_firewall [Rule (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8))) Drop]"



theorem to_simple_firewall: "check_simple_fw_preconditions rs \<Longrightarrow> approximating_bigstep_fun (common_matcher, \<alpha>) p rs Undecided = simple_fw (to_simple_firewall rs) p"
  proof(induction rs)
  case Nil thus ?case by(simp add: to_simple_firewall_simps)
  next
  case (Cons r rs)
    from Cons have IH: "approximating_bigstep_fun (common_matcher, \<alpha>) p rs Undecided = simple_fw (to_simple_firewall rs) p"
    by(simp add: check_simple_fw_preconditions_def)
    obtain m a where r: "r = Rule m a" by(cases r, simp)
    from Cons.prems have "check_simple_fw_preconditions [r]" by(simp add: check_simple_fw_preconditions_def)
    with r common_primitive_match_to_simple_match 
    have match: "\<And> sm. common_primitive_match_to_simple_match m = Some sm \<Longrightarrow> matches (common_matcher, \<alpha>) m a p = simple_matches sm p" and
         nomatch: "common_primitive_match_to_simple_match m = None \<Longrightarrow> \<not> matches (common_matcher, \<alpha>) m a p"
      unfolding check_simple_fw_preconditions_def by simp_all
    from to_simple_firewall_simps r Cons.prems have to_simple_firewall_simps': "to_simple_firewall (Rule m a # rs) =
        (case common_primitive_match_to_simple_match m of None \<Rightarrow> to_simple_firewall rs
                       | Some sm \<Rightarrow> SimpleRule sm (action_to_simple_action a) # to_simple_firewall rs)" by simp
    from `check_simple_fw_preconditions [r]` have "a = action.Accept \<or> a = action.Drop" by(simp add: r check_simple_fw_preconditions_def)
    thus ?case
      by(auto simp add: r to_simple_firewall_simps' IH match nomatch split: option.split action.split)
  qed

end

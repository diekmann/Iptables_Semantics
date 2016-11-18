section\<open>Iptables to Simple Firewall and Vice Versa\<close>
theory SimpleFw_Compliance
imports "../../Simple_Firewall/SimpleFw_Semantics"
        "../Primitive_Matchers/Transform"
        "../Primitive_Matchers/Primitive_Abstract"
begin

subsection\<open>Simple Match to MatchExpr\<close>

fun simple_match_to_ipportiface_match :: "'i::len simple_match \<Rightarrow> 'i common_primitive match_expr" where
  "simple_match_to_ipportiface_match \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr> =
    MatchAnd (Match (IIface iif)) (MatchAnd (Match (OIface oif)) 
    (MatchAnd (Match (Src (uncurry IpAddrNetmask sip)))
    (MatchAnd (Match (Dst (uncurry IpAddrNetmask dip)))
    (case p of ProtoAny \<Rightarrow> MatchAny
            |  Proto prim_p \<Rightarrow> 
                (MatchAnd (Match (Prot p))
                (MatchAnd (Match (Src_Ports (L4Ports prim_p [sps])))
                (Match (Dst_Ports (L4Ports prim_p [dps])))
                ))
    ))))"

lemma ports_to_set_singleton_simple_match_port: "p \<in> ports_to_set [a] \<longleftrightarrow> simple_match_port a p"
  by(cases a, simp)

theorem simple_match_to_ipportiface_match_correct:
  assumes valid: "simple_match_valid sm"
  shows "matches (common_matcher, \<alpha>) (simple_match_to_ipportiface_match sm) a p \<longleftrightarrow> simple_matches sm p"
  proof -
  obtain iif oif sip dip pro sps dps where
    sm: "sm = \<lparr>iiface = iif, oiface = oif, src = sip, dst = dip, proto = pro, sports = sps, dports = dps\<rparr>" by (cases sm)
  { fix ip
    have "p_src p \<in> ipt_iprange_to_set (uncurry IpAddrNetmask ip) \<longleftrightarrow> simple_match_ip ip (p_src p)"
    and  "p_dst p \<in> ipt_iprange_to_set (uncurry IpAddrNetmask ip) \<longleftrightarrow> simple_match_ip ip (p_dst p)"
     by(simp split: uncurry_split)+
  } note simple_match_ips=this
  { fix ps
    have "p_sport p \<in> ports_to_set [ps] \<longleftrightarrow> simple_match_port ps (p_sport p)"
    and  "p_dport p \<in> ports_to_set [ps] \<longleftrightarrow> simple_match_port ps (p_dport p)"
      apply(case_tac [!] ps)
      by(simp_all)
  } note simple_match_ports=this
  from valid sm have valid':"pro = ProtoAny \<Longrightarrow> simple_match_port sps (p_sport p) \<and> simple_match_port dps (p_dport p)"
    apply(simp add: simple_match_valid_def)
    by blast
  show ?thesis unfolding sm
  apply(cases pro)
   subgoal
   apply(simp add: bunch_of_lemmata_about_matches simple_matches.simps)
   apply(simp add: match_raw_bool ternary_to_bool_bool_to_ternary simple_match_ips simple_match_ports simple_matches.simps)
   using valid' by simp
  apply(simp add: bunch_of_lemmata_about_matches simple_matches.simps)
  apply(simp add: match_raw_bool ternary_to_bool_bool_to_ternary simple_match_ips simple_match_ports simple_matches.simps)
  apply fast
  done
qed



subsection\<open>MatchExpr to Simple Match\<close>

fun common_primitive_match_to_simple_match :: "'i::len common_primitive match_expr \<Rightarrow> 'i simple_match option" where
  "common_primitive_match_to_simple_match MatchAny = Some (simple_match_any)" |
  "common_primitive_match_to_simple_match (MatchNot MatchAny) = None" |
  "common_primitive_match_to_simple_match (Match (IIface iif)) = Some (simple_match_any\<lparr> iiface := iif \<rparr>)" |
  "common_primitive_match_to_simple_match (Match (OIface oif)) = Some (simple_match_any\<lparr> oiface := oif \<rparr>)" |
  "common_primitive_match_to_simple_match (Match (Src (IpAddrNetmask pre len))) = Some (simple_match_any\<lparr> src := (pre, len) \<rparr>)" |
  "common_primitive_match_to_simple_match (Match (Dst (IpAddrNetmask pre len))) = Some (simple_match_any\<lparr> dst := (pre, len) \<rparr>)" |
  "common_primitive_match_to_simple_match (Match (Prot p)) = Some (simple_match_any\<lparr> proto := p \<rparr>)" |
  "common_primitive_match_to_simple_match (Match (Src_Ports (L4Ports p []))) = None" |
  "common_primitive_match_to_simple_match (Match (Src_Ports (L4Ports p [(s,e)]))) = Some (simple_match_any\<lparr> proto := Proto p, sports := (s,e) \<rparr>)" |
  "common_primitive_match_to_simple_match (Match (Dst_Ports (L4Ports p []))) = None" |
  "common_primitive_match_to_simple_match (Match (Dst_Ports (L4Ports p [(s,e)]))) = Some (simple_match_any\<lparr> proto := Proto p, dports := (s,e) \<rparr>)" |
  "common_primitive_match_to_simple_match (MatchNot (Match (Prot ProtoAny))) = None" |
  "common_primitive_match_to_simple_match (MatchAnd m1 m2) = (case (common_primitive_match_to_simple_match m1, common_primitive_match_to_simple_match m2) of 
      (None, _) \<Rightarrow> None
    | (_, None) \<Rightarrow> None
    | (Some m1', Some m2') \<Rightarrow> simple_match_and m1' m2')" |
  --"undefined cases, normalize before!"
  "common_primitive_match_to_simple_match (Match (Src (IpAddr _))) = undefined" |
  "common_primitive_match_to_simple_match (Match (Src (IpAddrRange _ _))) = undefined" |
  "common_primitive_match_to_simple_match (Match (Dst (IpAddr _))) = undefined" |
  "common_primitive_match_to_simple_match (Match (Dst (IpAddrRange _ _))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (Prot _))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (IIface _))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (OIface _))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (Src _))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (Dst _))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (MatchAnd _ _)) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (MatchNot _)) = undefined" |
  "common_primitive_match_to_simple_match (Match (Src_Ports _)) = undefined" |
  "common_primitive_match_to_simple_match (Match (Dst_Ports _)) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (Src_Ports _))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (Dst_Ports _))) = undefined" |
  "common_primitive_match_to_simple_match (Match (CT_State _)) = undefined" |
  "common_primitive_match_to_simple_match (Match (L4_Flags _)) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (L4_Flags _))) = undefined" |
  "common_primitive_match_to_simple_match (Match (Extra _)) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (Extra _))) = undefined" |
  "common_primitive_match_to_simple_match (MatchNot (Match (CT_State _))) = undefined"



subsubsection\<open>Normalizing Interfaces\<close>
text\<open>As for now, negated interfaces are simply not allowed\<close>
  definition normalized_ifaces :: "'i::len common_primitive match_expr \<Rightarrow> bool" where
    "normalized_ifaces m \<equiv> \<not> has_disc_negated (\<lambda>a. is_Iiface a \<or> is_Oiface a) False m"

subsubsection\<open>Normalizing Protocols\<close>
text\<open>As for now, negated protocols are simply not allowed\<close>
  definition normalized_protocols :: "'i::len common_primitive match_expr \<Rightarrow> bool" where
    "normalized_protocols m \<equiv> \<not> has_disc_negated is_Prot False m"



lemma match_iface_simple_match_any_simps:
     "match_iface (iiface simple_match_any) (p_iiface p)"
     "match_iface (oiface simple_match_any) (p_oiface p)"
     "simple_match_ip (src simple_match_any) (p_src p)"
     "simple_match_ip (dst simple_match_any) (p_dst p)"
     "match_proto (proto simple_match_any) (p_proto p)"
     "simple_match_port (sports simple_match_any) (p_sport p)"
     "simple_match_port (dports simple_match_any) (p_dport p)"
  apply(simp_all add: simple_match_any_def match_ifaceAny ipset_from_cidr_0)
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
      and "\<not> has_disc is_L4_Flags m"
      and "\<not> has_disc is_CT_State m"
      and "\<not> has_disc is_MultiportPorts m"
      and "\<not> has_disc is_Extra m"
  shows "(Some sm = common_primitive_match_to_simple_match m \<longrightarrow> matches (common_matcher, \<alpha>) m a p \<longleftrightarrow> simple_matches sm p) \<and>
         (common_primitive_match_to_simple_match m = None \<longrightarrow> \<not> matches (common_matcher, \<alpha>) m a p)"
proof -
  show ?thesis
  using assms proof(induction m arbitrary: sm rule: common_primitive_match_to_simple_match.induct)
  case 1 thus ?case 
    by(simp add: match_iface_simple_match_any_simps bunch_of_lemmata_about_matches simple_matches.simps)
  next
  case (9 p s e) thus ?case
    apply(simp add: match_iface_simple_match_any_simps simple_matches.simps)
    apply(simp add: match_raw_bool ternary_to_bool_bool_to_ternary)
    by fastforce
  next
  case 11 thus ?case 
    apply(simp add: match_iface_simple_match_any_simps simple_matches.simps)
    apply(simp add: match_raw_bool ternary_to_bool_bool_to_ternary)
    by fastforce
  next
  case (13 m1 m2)
    let ?caseSome="Some sm = common_primitive_match_to_simple_match (MatchAnd m1 m2)"
    let ?caseNone="common_primitive_match_to_simple_match (MatchAnd m1 m2) = None"
    let ?goal="(?caseSome \<longrightarrow> matches (common_matcher, \<alpha>) (MatchAnd m1 m2) a p = simple_matches sm p) \<and> 
               (?caseNone \<longrightarrow> \<not> matches (common_matcher, \<alpha>) (MatchAnd m1 m2) a p)"

    from 13 have normalized:
      "normalized_src_ports m1" "normalized_src_ports m2"
      "normalized_dst_ports m1" "normalized_dst_ports m2"
      "normalized_src_ips m1" "normalized_src_ips m2"
      "normalized_dst_ips m1" "normalized_dst_ips m2"
      "normalized_ifaces m1" "normalized_ifaces m2"
      "\<not> has_disc is_L4_Flags m1" "\<not> has_disc is_L4_Flags m2"
      "\<not> has_disc is_CT_State m1" "\<not> has_disc is_CT_State m2"
      "\<not> has_disc is_MultiportPorts m1" "\<not> has_disc is_MultiportPorts m2"
      "\<not> has_disc is_Extra m1" "\<not> has_disc is_Extra m2"
      "normalized_protocols m1" "normalized_protocols m2"
      by(simp_all add: normalized_protocols_def normalized_ifaces_def)
    {  assume caseNone: ?caseNone
      { fix sm1 sm2
        assume sm1: "common_primitive_match_to_simple_match m1 = Some sm1"
           and sm2: "common_primitive_match_to_simple_match m2 = Some sm2"
           and sma: "simple_match_and sm1 sm2 = None"
        from sma have 1: "\<not> (simple_matches sm1 p \<and> simple_matches sm2 p)" by (simp add: simple_match_and_correct)
        from normalized sm1 sm2 "13.IH" have 2: "(matches (common_matcher, \<alpha>) m1 a p \<longleftrightarrow> simple_matches sm1 p) \<and> 
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
         using "13.IH" normalized by(simp add: bunch_of_lemmata_about_matches)+
    }note caseNone=this

    { assume caseSome: ?caseSome
      hence "\<exists> sm1. common_primitive_match_to_simple_match m1 = Some sm1" and
            "\<exists> sm2. common_primitive_match_to_simple_match m2 = Some sm2"
        by(simp_all split: option.split_asm)
      from this obtain sm1 sm2 where sm1: "Some sm1 = common_primitive_match_to_simple_match m1"
                                 and sm2: "Some sm2 = common_primitive_match_to_simple_match m2" by fastforce+
      with "13.IH" normalized have "matches (common_matcher, \<alpha>) m1 a p = simple_matches sm1 p \<and>
                    matches (common_matcher, \<alpha>) m2 a p = simple_matches sm2 p" by simp
      hence 1: "matches (common_matcher, \<alpha>) (MatchAnd m1 m2) a p \<longleftrightarrow> simple_matches sm1 p \<and> simple_matches sm2 p"
        by(simp add: bunch_of_lemmata_about_matches)
      from caseSome sm1 sm2 have "simple_match_and sm1 sm2 = Some sm" by(simp split: option.split_asm)
      hence 2: "simple_matches sm p \<longleftrightarrow> simple_matches sm1 p \<and> simple_matches sm2 p" by(simp add: simple_match_and_correct)
      from 1 2 have "matches (common_matcher, \<alpha>) (MatchAnd m1 m2) a p = simple_matches sm p" by simp
    } note caseSome=this

    from caseNone caseSome show ?goal by blast
  qed(simp_all add: match_iface_simple_match_any_simps simple_matches.simps normalized_protocols_def normalized_ifaces_def, 
      simp_all add: bunch_of_lemmata_about_matches, 
      simp_all add: match_raw_bool ternary_to_bool_bool_to_ternary)
qed

lemma simple_fw_remdups_Rev: "simple_fw (remdups_rev rs) p = simple_fw rs p"
  apply(induction rs p rule: simple_fw.induct)
    apply(simp add: remdups_rev_def)
   apply(simp_all add: remdups_rev_fst remdups_rev_removeAll simple_fw_not_matches_removeAll)
  done

fun action_to_simple_action :: "action \<Rightarrow> simple_action" where
  "action_to_simple_action action.Accept = simple_action.Accept" |
  "action_to_simple_action action.Drop   = simple_action.Drop" |
  "action_to_simple_action _ = undefined"

definition check_simple_fw_preconditions :: "'i::len common_primitive rule list \<Rightarrow> bool" where
  "check_simple_fw_preconditions rs \<equiv> \<forall>r \<in> set rs. (case r of (Rule m a) \<Rightarrow>
      normalized_src_ports m \<and>
      normalized_dst_ports m \<and>
      normalized_src_ips m \<and>
      normalized_dst_ips m \<and>
      normalized_ifaces m \<and> 
      normalized_protocols m \<and>
      \<not> has_disc is_L4_Flags m \<and>
      \<not> has_disc is_CT_State m \<and>
      \<not> has_disc is_MultiportPorts m \<and>
      \<not> has_disc is_Extra m \<and>
      (a = action.Accept \<or> a = action.Drop))"


(*apart from MatchNot MatchAny, the normalizations imply nnf*)
lemma "normalized_src_ports m \<Longrightarrow> normalized_nnf_match m"
  apply(induction m rule: normalized_src_ports.induct)
  apply(simp_all)[15]
  oops
lemma "\<not> matcheq_matchNone m \<Longrightarrow> normalized_src_ports m \<Longrightarrow> normalized_nnf_match m"
  by(induction m rule: normalized_src_ports.induct) (simp_all)

value "check_simple_fw_preconditions [Rule (MatchNot (MatchNot (MatchNot (Match (Src a))))) action.Accept]"


definition to_simple_firewall :: "'i::len common_primitive rule list \<Rightarrow> 'i simple_rule list" where
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


lemma "check_simple_fw_preconditions
     [Rule (MatchAnd (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8)))
                          (MatchAnd (Match (Dst_Ports (L4Ports TCP [(0, 65535)])))
                                    (Match (Src_Ports (L4Ports TCP [(0, 65535)])))))
                Drop]" by eval
lemma "to_simple_firewall
     [Rule (MatchAnd (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8)))
                          (MatchAnd (Match (Dst_Ports (L4Ports TCP [(0, 65535)])))
                                    (Match (Src_Ports (L4Ports TCP [(0, 65535)])))))
                Drop] =
[SimpleRule
   \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', src = (0x7F000000, 8), dst = (0, 0), proto = Proto 6, sports = (0, 0xFFFF),
      dports = (0, 0xFFFF)\<rparr>
   simple_action.Drop]" by eval
lemma "check_simple_fw_preconditions [Rule (MatchAnd MatchAny MatchAny) Drop]"
  by(simp add: check_simple_fw_preconditions_def normalized_ifaces_def normalized_protocols_def)
lemma "to_simple_firewall [Rule (MatchAnd MatchAny (MatchAny::32 common_primitive match_expr)) Drop] =
  [SimpleRule
   \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', src = (0, 0), dst = (0, 0), proto = ProtoAny, sports = (0, 0xFFFF),
      dports = (0, 0xFFFF)\<rparr>
   simple_action.Drop]" by eval
lemma "to_simple_firewall [Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8))) Drop] =
[SimpleRule
   \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', src = (0x7F000000, 8), dst = (0, 0), proto = ProtoAny, sports = (0, 0xFFFF),
      dports = (0, 0xFFFF)\<rparr>
   simple_action.Drop]" by eval



theorem to_simple_firewall: "check_simple_fw_preconditions rs \<Longrightarrow> approximating_bigstep_fun (common_matcher, \<alpha>) p rs Undecided = simple_fw (to_simple_firewall rs) p"
  proof(induction rs)
  case Nil thus ?case by(simp add: to_simple_firewall_simps)
  next
  case (Cons r rs)
    from Cons have IH: "approximating_bigstep_fun (common_matcher, \<alpha>) p rs Undecided = simple_fw (to_simple_firewall rs) p"
    by(simp add: check_simple_fw_preconditions_def)
    obtain m a where r: "r = Rule m a" by(cases r, simp)
    from Cons.prems have "check_simple_fw_preconditions [r]" by(simp add: check_simple_fw_preconditions_def)
    with r common_primitive_match_to_simple_match[where p = p]
    have match: "\<And> sm. common_primitive_match_to_simple_match m = Some sm \<Longrightarrow> matches (common_matcher, \<alpha>) m a p = simple_matches sm p" and
         nomatch: "common_primitive_match_to_simple_match m = None \<Longrightarrow> \<not> matches (common_matcher, \<alpha>) m a p"
      unfolding check_simple_fw_preconditions_def by simp_all
    from to_simple_firewall_simps r Cons.prems have to_simple_firewall_simps': "to_simple_firewall (Rule m a # rs) =
        (case common_primitive_match_to_simple_match m of None \<Rightarrow> to_simple_firewall rs
                       | Some sm \<Rightarrow> SimpleRule sm (action_to_simple_action a) # to_simple_firewall rs)" by simp
    from \<open>check_simple_fw_preconditions [r]\<close> have "a = action.Accept \<or> a = action.Drop" by(simp add: r check_simple_fw_preconditions_def)
    thus ?case
      by(auto simp add: r to_simple_firewall_simps' IH match nomatch split: option.split action.split)
  qed


lemma ctstate_assume_new_not_has_CT_State:
  "r \<in> set (ctstate_assume_new rs) \<Longrightarrow> \<not> has_disc is_CT_State (get_match r)"
  apply(simp add: ctstate_assume_new_def)
  apply(induction rs)
   apply(simp add: optimize_matches_def; fail)
  apply(simp add: optimize_matches_def)
  apply(rename_tac r' rs, case_tac r')
  apply(safe)
  apply(simp add:  split:if_split_asm)
  apply(elim disjE)
   apply(simp_all add: not_hasdisc_ctstate_assume_state split:if_split_asm)
  done

  

text\<open>The precondition for the simple firewall can be easily fulfilled.
      The subset relation is due to abstracting over some primitives (e.g., negated primitives, l4 flags)\<close>
theorem transform_simple_fw_upper:
  defines "preprocess rs \<equiv> upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new rs)))"
  and "newpkt p \<equiv> match_tcp_flags ipt_tcp_syn (p_tcp_flags p) \<and> p_tag_ctstate p = CT_New"
  assumes simplers: "simple_ruleset (rs:: 'i::len common_primitive rule list)"
  --"the preconditions for the simple firewall are fulfilled, definitely no runtime failure"
  shows "check_simple_fw_preconditions (preprocess rs)"
  --"the set of new packets, which are accepted is an overapproximations"
  and "{p. (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} \<subseteq>
       {p. simple_fw (to_simple_firewall (preprocess rs)) p = Decision FinalAllow \<and> newpkt p}"
  --\<open>Fun fact: The theorem holds for a tagged packet. The simple firewall just ignores the tag. 
     You may explicitly untag, if you wish to, but a @{typ "'i tagged_packet"} is just an extension of the
     @{typ "'i simple_packet"} used by the simple firewall\<close>
  unfolding check_simple_fw_preconditions_def preprocess_def
  apply(clarify, rename_tac r, case_tac r, rename_tac m a, simp)
  proof -
    let ?rs2="upper_closure (packet_assume_new rs)"
    let ?rs3="optimize_matches abstract_for_simple_firewall ?rs2"
    let ?rs'="upper_closure ?rs3"
    let ?\<gamma>="(common_matcher, in_doubt_allow)
            :: ('i::len common_primitive, ('i, 'a) tagged_packet_scheme) match_tac"
    let ?fw="\<lambda>rs p. approximating_bigstep_fun ?\<gamma> p rs Undecided"

    from packet_assume_new_simple_ruleset[OF simplers] have s1: "simple_ruleset (packet_assume_new rs)" .
    from transform_upper_closure(2)[OF s1] have s2: "simple_ruleset ?rs2" .
    from s2 have s3: "simple_ruleset ?rs3" by (simp add: optimize_matches_simple_ruleset) 
    from transform_upper_closure(2)[OF s3] have s4: "simple_ruleset ?rs'" .

    from transform_upper_closure(3)[OF s1] have nnf2:
      "\<forall>r\<in>set (upper_closure (packet_assume_new rs)). normalized_nnf_match (get_match r)" by simp
    
  { fix m a
    assume r: "Rule m a \<in> set ?rs'"

    from s4 r have a: "(a = action.Accept \<or> a = action.Drop)" by(auto simp add: simple_ruleset_def)
    
    have "r \<in> set (packet_assume_new rs) \<Longrightarrow> \<not> has_disc is_CT_State (get_match r)" for r
      by(simp add: packet_assume_new_def ctstate_assume_new_not_has_CT_State)
    with transform_upper_closure(4)[OF s1, where disc=is_CT_State] have
      "\<forall>r\<in>set (upper_closure (packet_assume_new rs)). \<not> has_disc is_CT_State (get_match r)"
      by simp
    with abstract_primitive_preserves_nodisc[where disc'="is_CT_State"]
    have "\<forall>r\<in>set ?rs3. \<not> has_disc is_CT_State (get_match r)"
      apply(intro optimize_matches_preserves)
      by(auto simp add: abstract_for_simple_firewall_def)
    with transform_upper_closure(4)[OF s3, where disc=is_CT_State] have
      "\<forall>r\<in>set ?rs'. \<not> has_disc is_CT_State (get_match r)" by simp
    with r have no_CT: "\<not> has_disc is_CT_State m" by fastforce

    from abstract_for_simple_firewall_hasdisc have "\<forall>r\<in>set ?rs3. \<not> has_disc is_L4_Flags (get_match r)"
      by(intro optimize_matches_preserves, auto)
    with transform_upper_closure(4)[OF s3, where disc=is_L4_Flags] have
      "\<forall>r\<in>set ?rs'. \<not> has_disc is_L4_Flags (get_match r)" by simp
    with r have no_L4_Flags: "\<not> has_disc is_L4_Flags m" by fastforce

    from nnf2 abstract_for_simple_firewall_negated_ifaces_prots have
      ifaces: "\<forall>r\<in>set ?rs3. \<not> has_disc_negated (\<lambda>a. is_Iiface a \<or> is_Oiface a) False (get_match r)" and
      protocols_rs3: "\<forall>r\<in>set ?rs3. \<not> has_disc_negated is_Prot False (get_match r)" 
      by(intro optimize_matches_preserves, blast)+
    from ifaces have iface_in:  "\<forall>r\<in>set ?rs3. \<not> has_disc_negated is_Iiface False (get_match r)" and
                     iface_out: "\<forall>r\<in>set ?rs3. \<not> has_disc_negated is_Oiface False (get_match r)"
    using has_disc_negated_disj_split by blast+

    from transform_upper_closure(3)[OF s3] have "\<forall>r\<in>set ?rs'.
     normalized_nnf_match (get_match r) \<and> normalized_src_ports (get_match r) \<and>
     normalized_dst_ports (get_match r) \<and> normalized_src_ips (get_match r) \<and>
     normalized_dst_ips (get_match r) \<and> 
     \<not> has_disc is_MultiportPorts (get_match r) \<and> \<not> has_disc is_Extra (get_match r)" .
    with r have normalized:
      "normalized_src_ports m \<and> normalized_dst_ports m \<and>
      normalized_src_ips m \<and> normalized_dst_ips m \<and> 
      \<not> has_disc is_MultiportPorts m & \<not> has_disc is_Extra m" by fastforce

    (*things are complicated because upper closure could introduce negated protocols.
      should not happen if we don't have negated ports in it *)
    from transform_upper_closure(5)[OF s3] iface_in iface_out have "\<forall>r\<in>set ?rs'.
     \<not> has_disc_negated is_Iiface False (get_match r) \<and> \<not> has_disc_negated is_Oiface False (get_match r)" by simp (*500ms*)
    with r have abstracted_ifaces: "normalized_ifaces m"
    unfolding normalized_ifaces_def has_disc_negated_disj_split by fastforce

    from transform_upper_closure(3)[OF s1]
      normalized_n_primitive_imp_not_disc_negated[OF wf_disc_sel_common_primitive(1)]
      normalized_n_primitive_imp_not_disc_negated[OF wf_disc_sel_common_primitive(2)]
    have "\<forall>r\<in> set ?rs2. \<not> has_disc_negated is_Src_Ports False (get_match r) \<and>
                        \<not> has_disc_negated is_Dst_Ports False (get_match r) \<and>
                        \<not> has_disc is_MultiportPorts (get_match r)"
      apply(simp add: normalized_src_ports_def2 normalized_dst_ports_def2)
      by blast 
    from this have "\<forall>r\<in>set ?rs3. \<not> has_disc_negated is_Src_Ports False (get_match r) \<and>
                                 \<not> has_disc_negated is_Dst_Ports False (get_match r) \<and>
                                 \<not> has_disc is_MultiportPorts (get_match r)"
      apply -
      apply(rule optimize_matches_preserves)
      apply(intro conjI)
        apply(intro abstract_for_simple_firewall_preserves_nodisc_negated, simp_all)+
      by (simp add: abstract_for_simple_firewall_def abstract_primitive_preserves_nodisc)

    from this protocols_rs3 transform_upper_closure(5)[OF s3, where disc=is_Prot, simplified]
          have "\<forall>r\<in>set ?rs'. \<not> has_disc_negated is_Prot False (get_match r)"
      by simp
    with r have abstracted_prots: "normalized_protocols m"
    unfolding normalized_protocols_def has_disc_negated_disj_split by fastforce
    
    from no_CT no_L4_Flags s4 normalized a abstracted_ifaces abstracted_prots show "normalized_src_ports m \<and>
             normalized_dst_ports m \<and>
             normalized_src_ips m \<and>
             normalized_dst_ips m \<and>
             normalized_ifaces m \<and>
             normalized_protocols m \<and>
             \<not> has_disc is_L4_Flags m \<and>
             \<not> has_disc is_CT_State m \<and>
             \<not> has_disc is_MultiportPorts m \<and>
             \<not> has_disc is_Extra m \<and> (a = action.Accept \<or> a = action.Drop)"
      by(simp)
  }
    hence simple_fw_preconditions: "check_simple_fw_preconditions ?rs'"
    unfolding check_simple_fw_preconditions_def
    by(clarify, rename_tac r, case_tac r, rename_tac m a, simp)


    have 1: "{p. ?\<gamma>,p\<turnstile> \<langle>?rs', Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} =
          {p. ?\<gamma>,p\<turnstile> \<langle>?rs3, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      apply(subst transform_upper_closure(1)[OF s3])
      by simp
    from abstract_primitive_in_doubt_allow_generic(2)[OF primitive_matcher_generic_common_matcher nnf2 s2] have 2:
         "{p. ?\<gamma>,p\<turnstile> \<langle>upper_closure (packet_assume_new rs), Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} \<subseteq>
          {p. ?\<gamma>,p\<turnstile> \<langle>?rs3, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      by(auto simp add: abstract_for_simple_firewall_def)
    have 3: "{p. ?\<gamma>,p\<turnstile> \<langle>upper_closure (packet_assume_new rs), Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} =
          {p. ?\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      apply(subst transform_upper_closure(1)[OF s1])
      apply(subst approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF s1]])
      apply(subst approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers]])
      using packet_assume_new newpkt_def by fastforce
      
    have 4: "\<And>p. ?\<gamma>,p\<turnstile> \<langle>?rs', Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<longleftrightarrow> ?fw ?rs' p = Decision FinalAllow"
      using approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF s4]] by fast
    
    have "{p. ?\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} \<subseteq>
       {p. ?\<gamma>,p\<turnstile> \<langle>?rs', Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      apply(subst 1)
      apply(subst 3[symmetric])
      using 2 by blast
    
    thus "{p. ?\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} \<subseteq>
       {p. simple_fw (to_simple_firewall ?rs') p = Decision FinalAllow \<and> newpkt p}"
       apply safe
       subgoal for p using to_simple_firewall[OF simple_fw_preconditions, where p = p] 4 by auto
      done
  qed


(*Copy&paste from transform_simple_fw_upper*)
theorem transform_simple_fw_lower:
  defines "preprocess rs \<equiv> lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new rs)))"
  and "newpkt p \<equiv> match_tcp_flags ipt_tcp_syn (p_tcp_flags p) \<and> p_tag_ctstate p = CT_New"
  assumes simplers: "simple_ruleset (rs:: 'i::len common_primitive rule list)"
  --"the preconditions for the simple firewall are fulfilled, definitely no runtime failure"
  shows "check_simple_fw_preconditions (preprocess rs)"
  --"the set of new packets, which are accepted is an underapproximation"
  and "{p. simple_fw (to_simple_firewall (preprocess rs)) p = Decision FinalAllow \<and> newpkt p} \<subseteq>
       {p. (common_matcher, in_doubt_deny),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
  unfolding check_simple_fw_preconditions_def preprocess_def
  apply(clarify, rename_tac r, case_tac r, rename_tac m a, simp)
  proof -
    let ?rs2="lower_closure (packet_assume_new rs)"
    let ?rs3="optimize_matches abstract_for_simple_firewall ?rs2"
    let ?rs'="lower_closure ?rs3"
    let ?\<gamma>="(common_matcher, in_doubt_deny)
            :: ('i::len common_primitive, ('i, 'a) tagged_packet_scheme) match_tac"
    let ?fw="\<lambda>rs p. approximating_bigstep_fun ?\<gamma> p rs Undecided"

    from packet_assume_new_simple_ruleset[OF simplers] have s1: "simple_ruleset (packet_assume_new rs)" .
    from transform_lower_closure(2)[OF s1] have s2: "simple_ruleset (lower_closure (packet_assume_new rs))" .
    from s2 have s3: "simple_ruleset ?rs3" by (simp add: optimize_matches_simple_ruleset) 
    from transform_lower_closure(2)[OF s3] have s4: "simple_ruleset ?rs'" .

    from transform_lower_closure(3)[OF s1] have nnf2:
      "\<forall>r\<in>set (lower_closure (packet_assume_new rs)). normalized_nnf_match (get_match r)" by simp
    
  { fix m a
    assume r: "Rule m a \<in> set ?rs'"

    from s4 r have a: "(a = action.Accept \<or> a = action.Drop)" by(auto simp add: simple_ruleset_def)
    
    have "r \<in> set (packet_assume_new rs) \<Longrightarrow> \<not> has_disc is_CT_State (get_match r)" for r 
      by(simp add: packet_assume_new_def ctstate_assume_new_not_has_CT_State)
    with transform_lower_closure(4)[OF s1, where disc=is_CT_State] have
      "\<forall>r\<in>set (lower_closure (packet_assume_new rs)). \<not> has_disc is_CT_State (get_match r)"
      by fastforce
    with abstract_primitive_preserves_nodisc[where disc'="is_CT_State"] have
      "\<forall>r\<in>set ?rs3. \<not> has_disc is_CT_State (get_match r)"
      apply(intro optimize_matches_preserves)
      by(auto simp add: abstract_for_simple_firewall_def)
    with transform_lower_closure(4)[OF s3, where disc=is_CT_State] have
      "\<forall>r\<in>set ?rs'. \<not> has_disc is_CT_State (get_match r)" by fastforce
    with r have no_CT: "\<not> has_disc is_CT_State m" by fastforce

    from abstract_for_simple_firewall_hasdisc have "\<forall>r\<in>set ?rs3. \<not> has_disc is_L4_Flags (get_match r)"
      by(intro optimize_matches_preserves, blast)
    with transform_lower_closure(4)[OF s3, where disc=is_L4_Flags] have
      "\<forall>r\<in>set ?rs'. \<not> has_disc is_L4_Flags (get_match r)" by fastforce
    with r have no_L4_Flags: "\<not> has_disc is_L4_Flags m" by fastforce

    from nnf2 abstract_for_simple_firewall_negated_ifaces_prots have
      ifaces: "\<forall>r\<in>set ?rs3. \<not> has_disc_negated (\<lambda>a. is_Iiface a \<or> is_Oiface a) False (get_match r)" and
      protocols_rs3: "\<forall>r\<in>set ?rs3. \<not> has_disc_negated is_Prot False (get_match r)" 
      by(intro optimize_matches_preserves, blast)+
    from ifaces have iface_in:  "\<forall>r\<in>set ?rs3. \<not> has_disc_negated is_Iiface False (get_match r)" and
                     iface_out: "\<forall>r\<in>set ?rs3. \<not> has_disc_negated is_Oiface False (get_match r)"
    using has_disc_negated_disj_split by blast+

    from transform_lower_closure(3)[OF s3] have "\<forall>r\<in>set ?rs'.
     normalized_nnf_match (get_match r) \<and> normalized_src_ports (get_match r) \<and>
     normalized_dst_ports (get_match r) \<and> normalized_src_ips (get_match r) \<and>
     normalized_dst_ips (get_match r) \<and> 
     \<not> has_disc is_MultiportPorts (get_match r) \<and> \<not> has_disc is_Extra (get_match r)" .
    with r have normalized: "normalized_src_ports m \<and> normalized_dst_ports m \<and> normalized_src_ips m \<and>
      normalized_dst_ips m \<and> \<not> has_disc is_MultiportPorts m \<and> \<not> has_disc is_Extra m" by fastforce


    from transform_lower_closure(5)[OF s3] iface_in iface_out have "\<forall>r\<in>set ?rs'.
     \<not> has_disc_negated is_Iiface False (get_match r) \<and> \<not> has_disc_negated is_Oiface False (get_match r)" by simp (*500ms*)
    with r have abstracted_ifaces: "normalized_ifaces m"
    unfolding normalized_ifaces_def has_disc_negated_disj_split by fastforce

    from transform_lower_closure(3)[OF s1]
      normalized_n_primitive_imp_not_disc_negated[OF wf_disc_sel_common_primitive(1)]
      normalized_n_primitive_imp_not_disc_negated[OF wf_disc_sel_common_primitive(2)]
    have "\<forall>r\<in>set ?rs2. \<not> has_disc_negated is_Src_Ports False (get_match r) \<and>
                       \<not> has_disc_negated is_Dst_Ports False (get_match r) \<and>
                       \<not> has_disc is_MultiportPorts (get_match r)"
      apply(simp add: normalized_src_ports_def2 normalized_dst_ports_def2)
      by blast 
    from this have "\<forall>r\<in>set ?rs3. \<not> has_disc_negated is_Src_Ports False (get_match r) \<and>
                                 \<not> has_disc_negated is_Dst_Ports False (get_match r) \<and>
                                 \<not> has_disc is_MultiportPorts (get_match r)"
      apply -
      apply(rule optimize_matches_preserves)
      apply(intro conjI)
        apply(intro abstract_for_simple_firewall_preserves_nodisc_negated, simp_all)+
      by (simp add: abstract_for_simple_firewall_def abstract_primitive_preserves_nodisc)
    from this protocols_rs3 transform_lower_closure(5)[OF s3, where disc=is_Prot, simplified]
          have "\<forall>r\<in>set ?rs'. \<not> has_disc_negated is_Prot False (get_match r)"
      by simp
    with r have abstracted_prots: "normalized_protocols m"
    unfolding normalized_protocols_def has_disc_negated_disj_split by fastforce
    
    from no_CT no_L4_Flags s4 normalized a abstracted_ifaces abstracted_prots show "normalized_src_ports m \<and>
             normalized_dst_ports m \<and>
             normalized_src_ips m \<and>
             normalized_dst_ips m \<and>
             normalized_ifaces m \<and>
             normalized_protocols m \<and> \<not> has_disc is_L4_Flags m \<and> \<not> has_disc is_CT_State m \<and> 
             \<not> has_disc is_MultiportPorts m \<and> \<not> has_disc is_Extra m \<and> (a = action.Accept \<or> a = action.Drop)"
      by(simp)
  }
    hence simple_fw_preconditions: "check_simple_fw_preconditions ?rs'"
    unfolding check_simple_fw_preconditions_def
    by(clarify, rename_tac r, case_tac r, rename_tac m a, simp)

    have 1: "{p. ?\<gamma>,p\<turnstile> \<langle>?rs', Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} =
          {p. ?\<gamma>,p\<turnstile> \<langle>?rs3, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      apply(subst transform_lower_closure(1)[OF s3])
      by simp
    from abstract_primitive_in_doubt_deny_generic(1)[OF primitive_matcher_generic_common_matcher nnf2 s2] have 2:
         "{p. ?\<gamma>,p\<turnstile> \<langle>?rs3, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} \<subseteq>
          {p. ?\<gamma>,p\<turnstile> \<langle>lower_closure (packet_assume_new rs), Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      by(auto simp add: abstract_for_simple_firewall_def)
    have 3: "{p. ?\<gamma>,p\<turnstile> \<langle>lower_closure (packet_assume_new rs), Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} =
          {p. ?\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      apply(subst transform_lower_closure(1)[OF s1])
      apply(subst approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF s1]])
      apply(subst approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers]])
      using packet_assume_new newpkt_def by fastforce
      
    have 4: "\<And>p. ?\<gamma>,p\<turnstile> \<langle>?rs', Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<longleftrightarrow> ?fw ?rs' p = Decision FinalAllow"
      using approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF s4]] by fast
    
    have "{p. ?\<gamma>,p\<turnstile> \<langle>?rs', Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} \<subseteq>
          {p. ?\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      apply(subst 1)
      apply(subst 3[symmetric])
      using 2 by blast
    
    thus "{p. simple_fw (to_simple_firewall ?rs') p = Decision FinalAllow \<and> newpkt p} \<subseteq>
          {p. ?\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} "
      apply safe
      subgoal for p using to_simple_firewall[OF simple_fw_preconditions, where p = p] 4 by auto
    done
  qed


definition "to_simple_firewall_without_interfaces ipassmt rtblo rs \<equiv>
    to_simple_firewall
    (upper_closure
    (optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a))
    (optimize_matches abstract_for_simple_firewall
    (upper_closure
    (iface_try_rewrite ipassmt rtblo
    (upper_closure
    (packet_assume_new rs)))))))"



(*basically a copy&paste from transform_simple_fw_upper. but this one is way cleaner! refactor the other using this!*)
theorem to_simple_firewall_without_interfaces:
  defines "newpkt p \<equiv> match_tcp_flags ipt_tcp_syn (p_tcp_flags p) \<and> p_tag_ctstate p = CT_New"
  assumes simplers: "simple_ruleset (rs:: 'i::len common_primitive rule list)"

      --"well-formed ipassmt"
      and wf_ipassmt1: "ipassmt_sanity_nowildcards (map_of ipassmt)" and wf_ipassmt2: "distinct (map fst ipassmt)"
      --"There are no spoofed packets (probably by kernel's reverse path filter or our checker).
         This assumption implies that ipassmt lists ALL interfaces (!!)."
      and nospoofing: "\<forall>(p::('i::len, 'a) tagged_packet_scheme).
            \<exists>ips. (map_of ipassmt) (Iface (p_iiface p)) = Some ips \<and> p_src p \<in> ipcidr_union_set (set ips)"
      --"If a routing table was passed, the output interface for any packet we consider is decided based on it."
      and routing_decided: "\<And>rtbl (p::('i,'a) tagged_packet_scheme). rtblo = Some rtbl \<Longrightarrow> output_iface (routing_table_semantics rtbl (p_dst p)) = p_oiface p"
      --"A passed routing table is wellformed"
      and correct_routing: "\<And>rtbl. rtblo = Some rtbl \<Longrightarrow> correct_routing rtbl"
      --"A passed routing table contains no interfaces with wildcard names"
      and routing_no_wildcards: "\<And>rtbl. rtblo = Some rtbl \<Longrightarrow> ipassmt_sanity_nowildcards (map_of (routing_ipassmt rtbl))"

  --"the set of new packets, which are accepted is an overapproximations"
  shows "{p::('i,'a) tagged_packet_scheme. (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} \<subseteq>
         {p::('i,'a) tagged_packet_scheme. simple_fw (to_simple_firewall_without_interfaces ipassmt rtblo rs) p = Decision FinalAllow \<and> newpkt p}"

  and "\<forall>r \<in> set (to_simple_firewall_without_interfaces ipassmt rtblo rs).
          iiface (match_sel r) = ifaceAny \<and> oiface (match_sel r) = ifaceAny"
  proof -
    let ?rs1="packet_assume_new rs"
    let ?rs2="upper_closure ?rs1"
    let ?rs3="iface_try_rewrite ipassmt rtblo ?rs2"
    let ?rs4="upper_closure ?rs3"
    let ?rs5="optimize_matches abstract_for_simple_firewall ?rs4"
    let ?rs6="optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a)) ?rs5"
    let ?rs7="upper_closure ?rs6"
    let ?\<gamma>="(common_matcher, in_doubt_allow)
          :: ('i::len common_primitive, ('i, 'a) tagged_packet_scheme) match_tac"

    have "to_simple_firewall_without_interfaces ipassmt rtblo rs = to_simple_firewall ?rs7"
      by(simp add: to_simple_firewall_without_interfaces_def)

    from packet_assume_new_simple_ruleset[OF simplers] have s1: "simple_ruleset ?rs1" .
    from transform_upper_closure(2)[OF s1] have s2: "simple_ruleset ?rs2" .
    from iface_try_rewrite_simplers[OF s2] have s3: "simple_ruleset ?rs3" .
    from transform_upper_closure(2)[OF s3] have s4: "simple_ruleset ?rs4" .
    from optimize_matches_simple_ruleset[OF s4] have s5: "simple_ruleset ?rs5" .
    from optimize_matches_simple_ruleset[OF s5] have s6: "simple_ruleset ?rs6" .
    from transform_upper_closure(2)[OF s6] have s7: "simple_ruleset ?rs7" .

    from transform_upper_closure(3)[OF s1] have nnf2: "\<forall>r\<in>set ?rs2. normalized_nnf_match (get_match r)" by simp
    from transform_upper_closure(3)[OF s3] have nnf4: "\<forall>r\<in>set ?rs4. normalized_nnf_match (get_match r)" by simp
    have nnf5: "\<forall>r\<in>set ?rs5. normalized_nnf_match (get_match r)"
      apply(intro optimize_matches_preserves)
      apply(simp add: abstract_for_simple_firewall_def)
      apply(rule abstract_primitive_preserves_normalized(5))
      using nnf4 by(simp)
    have nnf6: "\<forall>r\<in>set ?rs6. normalized_nnf_match (get_match r)"
      apply(intro optimize_matches_preserves)
      apply(rule abstract_primitive_preserves_normalized(5))
      using nnf5 by(simp)
    from transform_upper_closure(3)[OF s6] have nnf7: "\<forall>r\<in>set ?rs7. normalized_nnf_match (get_match r)" by simp


    (*subgoal @{term "check_simple_fw_preconditions ?rs7"}*)
    { fix m a
      assume r: "Rule m a \<in> set ?rs7"
  
      from s7 r have a: "(a = action.Accept \<or> a = action.Drop)" by(auto simp add: simple_ruleset_def)
      
      from abstract_for_simple_firewall_hasdisc have "\<forall>r\<in>set ?rs5. \<not> has_disc is_CT_State (get_match r)"
        by(intro optimize_matches_preserves, blast)
      with abstract_primitive_preserves_nodisc[where disc'="is_CT_State"] have
        "\<forall>r\<in>set ?rs6. \<not> has_disc is_CT_State (get_match r)"
        apply(intro optimize_matches_preserves)
        apply(simp)
        by blast
      with transform_upper_closure(4)[OF s6, where disc=is_CT_State] have
        "\<forall>r\<in>set ?rs7. \<not> has_disc is_CT_State (get_match r)" by simp
      with r have no_CT: "\<not> has_disc is_CT_State m" by fastforce

      from abstract_for_simple_firewall_hasdisc have "\<forall>r\<in>set ?rs5. \<not> has_disc is_L4_Flags (get_match r)"
        by(intro optimize_matches_preserves, blast)
      with abstract_primitive_preserves_nodisc[where disc'="is_L4_Flags"] have
        "\<forall>r\<in>set ?rs6. \<not> has_disc is_L4_Flags (get_match r)"
        by(intro optimize_matches_preserves) auto
      with transform_upper_closure(4)[OF s6, where disc=is_L4_Flags] have
        "\<forall>r\<in>set ?rs7. \<not> has_disc is_L4_Flags (get_match r)" by simp
      with r have no_L4_Flags: "\<not> has_disc is_L4_Flags m" by fastforce


      have "\<forall>r\<in>set ?rs6. \<not> has_disc is_Iiface (get_match r)"
        by(intro optimize_matches_preserves abstract_primitive_nodisc) simp+
      with transform_upper_closure(4)[OF s6, where disc=is_Iiface] have
        "\<forall>r\<in>set ?rs7. \<not> has_disc is_Iiface (get_match r)" by simp
      with r have no_Iiface: "\<not> has_disc is_Iiface m" by fastforce

      have "\<forall>r\<in>set ?rs6. \<not> has_disc is_Oiface (get_match r)"
        by(intro optimize_matches_preserves abstract_primitive_nodisc) simp+
      with transform_upper_closure(4)[OF s6, where disc=is_Oiface] have
        "\<forall>r\<in>set ?rs7. \<not> has_disc is_Oiface (get_match r)" by simp
      with r have no_Oiface: "\<not> has_disc is_Oiface m" by fastforce

      from no_Iiface no_Oiface have normalized_ifaces: "normalized_ifaces m"
        using has_disc_negated_disj_split has_disc_negated_has_disc normalized_ifaces_def by blast

      from transform_upper_closure(3)[OF s6] r have normalized:
        "normalized_src_ports m \<and> normalized_dst_ports m \<and>
         normalized_src_ips m \<and> normalized_dst_ips m \<and>
         \<not> has_disc is_MultiportPorts m \<and> \<not> has_disc is_Extra m" by fastforce


      from transform_upper_closure(3)[OF s3, simplified]
        normalized_n_primitive_imp_not_disc_negated[OF wf_disc_sel_common_primitive(1)]
        normalized_n_primitive_imp_not_disc_negated[OF wf_disc_sel_common_primitive(2)]
      have "\<forall>r \<in> set ?rs4. \<not> has_disc_negated is_Src_Ports False (get_match r) \<and>
                           \<not> has_disc_negated is_Dst_Ports False (get_match r) \<and>
                           \<not> has_disc is_MultiportPorts (get_match r)"
        apply(simp add: normalized_src_ports_def2 normalized_dst_ports_def2)
        by blast
      hence "\<forall>r \<in> set ?rs5. \<not> has_disc_negated is_Src_Ports False (get_match r) \<and>
                            \<not> has_disc_negated is_Dst_Ports False (get_match r) \<and>
                            \<not> has_disc is_MultiportPorts (get_match r)"
        apply -
        apply(rule optimize_matches_preserves)
        apply(intro conjI)
          apply(intro abstract_for_simple_firewall_preserves_nodisc_negated, simp_all)+
        by (simp add: abstract_for_simple_firewall_def abstract_primitive_preserves_nodisc)
      from this have no_ports_rs6: 
            "\<forall>r \<in> set ?rs6. \<not> has_disc_negated is_Src_Ports False (get_match r) \<and>
                            \<not> has_disc_negated is_Dst_Ports False (get_match r) \<and>
                            \<not> has_disc is_MultiportPorts (get_match r)"
        apply -
        apply(rule optimize_matches_preserves)
        apply(intro conjI)
          apply(intro abstract_primitive_preserves_nodisc_nedgated, simp_all)+
        by (simp add: abstract_for_simple_firewall_def abstract_primitive_preserves_nodisc)

      from nnf4 abstract_for_simple_firewall_negated_ifaces_prots(2) have 
        "\<forall>r\<in>set ?rs5. \<not> has_disc_negated is_Prot False (get_match r)"
        by(intro optimize_matches_preserves) blast
      hence "\<forall>r\<in>set ?rs6. \<not> has_disc_negated is_Prot False (get_match r)"
        by(intro optimize_matches_preserves abstract_primitive_preserves_nodisc_nedgated) simp+
      with no_ports_rs6 have "\<forall>r\<in>set ?rs7. \<not> has_disc_negated is_Prot False (get_match r)"
       by(intro transform_upper_closure(5)[OF s6]) simp+
      with r have protocols: "normalized_protocols m" unfolding normalized_protocols_def by fastforce


      from no_CT no_L4_Flags normalized a normalized_ifaces protocols no_Iiface no_Oiface 
         have "normalized_src_ports m \<and>
               normalized_dst_ports m \<and>
               normalized_src_ips m \<and>
               normalized_dst_ips m \<and>
               normalized_ifaces m \<and>
               normalized_protocols m \<and>
               \<not> has_disc is_L4_Flags m \<and>
               \<not> has_disc is_CT_State m \<and>
               \<not> has_disc is_MultiportPorts m \<and>
               \<not> has_disc is_Extra m \<and> (a = action.Accept \<or> a = action.Drop)"
        and "\<not> has_disc is_Iiface m" and "\<not> has_disc is_Oiface m"
        apply -
        by(simp)+ (*fails due to is_MultiportPorts*)
    }
    hence simple_fw_preconditions: "check_simple_fw_preconditions ?rs7"
      and no_interfaces: "Rule m a \<in> set ?rs7 \<Longrightarrow> \<not> has_disc is_Iiface m \<and> \<not> has_disc is_Oiface m" for m a
    apply -
     subgoal unfolding check_simple_fw_preconditions_def by(clarify, rename_tac r, case_tac r, rename_tac m a, simp)
    by simp


    have "{p :: ('i,'a) tagged_packet_scheme. ?\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} =
          {p :: ('i,'a) tagged_packet_scheme. ?\<gamma>,p\<turnstile> \<langle>?rs1, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      apply(subst approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF s1]])
      apply(subst approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers]])
      apply(rule Collect_cong)
      subgoal for p using packet_assume_new[where p = p] newpkt_def[where p = p] by auto
      done
    also have "{p. ?\<gamma>,p\<turnstile> \<langle>?rs1, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} =
          {p. ?\<gamma>,p\<turnstile> \<langle>?rs2, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      apply(subst transform_upper_closure(1)[OF s1])
      by simp
    also have "\<dots> = {p. ?\<gamma>,p\<turnstile> \<langle>?rs3, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      apply(cases rtblo; simp; (subst iface_try_rewrite_rtbl[OF s2 nnf2] | subst iface_try_rewrite_no_rtbl[OF s2 nnf2]))
        using wf_ipassmt1 wf_ipassmt2 nospoofing wf_in_doubt_allow routing_no_wildcards correct_routing routing_decided by simp_all
    also have "\<dots> = {p. ?\<gamma>,p\<turnstile> \<langle>?rs4, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      apply(subst transform_upper_closure(1)[OF s3])
      by simp
    finally have 1: "{p. ?\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} =
                  {p. ?\<gamma>,p\<turnstile> \<langle>?rs4, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}" .
    from abstract_primitive_in_doubt_allow_generic(2)[OF primitive_matcher_generic_common_matcher nnf4 s4] have 2:
         "{p. ?\<gamma>,p\<turnstile> \<langle>?rs4, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} \<subseteq>
          {p. ?\<gamma>,p\<turnstile> \<langle>?rs5, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      by(auto simp add: abstract_for_simple_firewall_def)
    from abstract_primitive_in_doubt_allow_generic(2)[OF primitive_matcher_generic_common_matcher nnf5 s5] have 3:
         "{p. ?\<gamma>,p\<turnstile> \<langle>?rs5, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} \<subseteq>
          {p. ?\<gamma>,p\<turnstile> \<langle>?rs6, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      by(auto simp add: abstract_for_simple_firewall_def)
    have 4: "{p. ?\<gamma>,p\<turnstile> \<langle>?rs6, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} =
             {p. ?\<gamma>,p\<turnstile> \<langle>?rs7, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
      apply(subst transform_upper_closure(1)[OF s6])
      by simp

      
    let ?fw="\<lambda>rs p. approximating_bigstep_fun ?\<gamma> p rs Undecided"
    have approximating_rule: "\<And>p. ?\<gamma>,p\<turnstile> \<langle>?rs7, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<longleftrightarrow> ?fw ?rs7 p = Decision FinalAllow"
      using approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF s7]] by fast
    
    from 1 2 3 4 have "{p. ?\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} \<subseteq>
       {p. ?\<gamma>,p\<turnstile> \<langle>?rs7, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}" by blast
    
    thus "{p. (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} \<subseteq>
         {p. simple_fw (to_simple_firewall_without_interfaces ipassmt rtblo rs) p = Decision FinalAllow \<and> newpkt p}"
      apply(safe)
      subgoal for p   
       unfolding to_simple_firewall_without_interfaces_def
       using to_simple_firewall[OF simple_fw_preconditions, where p = p] approximating_rule[where p = p] by auto
      done

    (*the following proof to show that we don't have interfaces left is MADNESS*)

    have common_primitive_match_to_simple_match_nodisc: 
      "Some sm = common_primitive_match_to_simple_match m' \<Longrightarrow>
       \<not> has_disc is_Iiface m' \<and> \<not> has_disc is_Oiface m' \<Longrightarrow> iiface sm = ifaceAny \<and> oiface sm = ifaceAny"
    if prems: "check_simple_fw_preconditions [Rule m' a']"
    for m' :: "'i common_primitive match_expr" and a' sm
    using prems proof(induction m' arbitrary: sm rule: common_primitive_match_to_simple_match.induct)
    case 18 thus ?case
    by(simp add: check_simple_fw_preconditions_def normalized_protocols_def)
    next
    case (13 m1 m2) thus ?case
      (*This is madness!!*)
      apply(simp add: check_simple_fw_preconditions_def)
      apply(case_tac "common_primitive_match_to_simple_match m1")
       apply(simp; fail)
      apply(case_tac "common_primitive_match_to_simple_match m2")
       apply(simp; fail)
      apply simp
      apply(rename_tac a aa)
      apply(case_tac a)
      apply(case_tac aa)
      apply(simp)
      apply(simp split: option.split_asm)
      using iface_conjunct_ifaceAny normalized_ifaces_def normalized_protocols_def
      by (metis has_disc_negated.simps(4) option.inject)
    qed(simp_all add: check_simple_fw_preconditions_def simple_match_any_def)

    have to_simple_firewall_no_ifaces: "(\<And>m a. Rule m a \<in> set rs \<Longrightarrow> \<not> has_disc is_Iiface m \<and> \<not> has_disc is_Oiface m) \<Longrightarrow> 
        \<forall>r\<in>set (to_simple_firewall rs). iiface (match_sel r) = ifaceAny \<and> oiface (match_sel r) = ifaceAny"
      if pre1: "check_simple_fw_preconditions rs" for rs :: "'i common_primitive rule list"
    using pre1 apply(induction rs)
     apply(simp add: to_simple_firewall_simps; fail)
    apply simp
    apply(subgoal_tac "check_simple_fw_preconditions rs")
     prefer 2
     subgoal by(simp add: check_simple_fw_preconditions_def)
    apply(rename_tac r rs, case_tac r)
    apply simp
    apply(simp add: to_simple_firewall_simps)
    apply(simp split: option.split)
    apply(intro conjI)
     apply blast
    apply(intro allI impI)
    apply(subgoal_tac "(\<forall>m\<in>set (to_simple_firewall rs). iiface (match_sel m) = ifaceAny \<and> oiface (match_sel m) = ifaceAny)")
     prefer 2
     subgoal by blast
    apply(simp)
    apply(rename_tac m' a' sm)
    apply(subgoal_tac " \<not> has_disc is_Iiface m' \<and> \<not> has_disc is_Oiface m'")
     prefer 2
     subgoal by blast
    apply(subgoal_tac "check_simple_fw_preconditions [Rule m' a']")
     prefer 2
     subgoal by(simp add: check_simple_fw_preconditions_def)
    apply(drule common_primitive_match_to_simple_match_nodisc)
      apply(simp_all)
    done
   
    from to_simple_firewall_no_ifaces[OF simple_fw_preconditions no_interfaces] show 
      "\<forall>r \<in> set (to_simple_firewall_without_interfaces ipassmt rtblo rs). iiface (match_sel r) = ifaceAny \<and> oiface (match_sel r) = ifaceAny"
      unfolding to_simple_firewall_without_interfaces_def
      by(simp add: to_simple_firewall_def simple_fw_preconditions)
      
  qed



end

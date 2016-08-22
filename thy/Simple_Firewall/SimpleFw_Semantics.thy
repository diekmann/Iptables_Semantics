section\<open>Simple Firewall Semantics\<close>
theory SimpleFw_Semantics
imports SimpleFw_Syntax
        "../IP_Addresses/IP_Address"
        "../IP_Addresses/Prefix_Match"
begin


  fun simple_match_ip :: "('i::len word \<times> nat) \<Rightarrow> 'i::len word \<Rightarrow> bool" where
    "simple_match_ip (base, len) p_ip \<longleftrightarrow> p_ip \<in> ipset_from_cidr base len"

  lemma wordinterval_to_set_ipcidr_tuple_to_wordinterval_simple_match_ip_set:
    "wordinterval_to_set (ipcidr_tuple_to_wordinterval ip) = {d. simple_match_ip ip d}"
    proof -
      { fix s and d :: "'a::len word \<times> nat"
        from wordinterval_to_set_ipcidr_tuple_to_wordinterval have
          "s \<in> wordinterval_to_set (ipcidr_tuple_to_wordinterval d) \<longleftrightarrow> simple_match_ip d s"
        by(cases d) auto
      } thus ?thesis by blast
    qed

  --"by the way, the words do not wrap around"
  lemma "{(253::8 word) .. 8} = {}" by simp 

  fun simple_match_port :: "(16 word \<times> 16 word) \<Rightarrow> 16 word \<Rightarrow> bool" where
    "simple_match_port (s,e) p_p \<longleftrightarrow> p_p \<in> {s..e}"

  fun simple_matches :: "'i::len simple_match \<Rightarrow> ('i, 'a) simple_packet_scheme \<Rightarrow> bool" where
    "simple_matches m p \<longleftrightarrow>
      (match_iface (iiface m) (p_iiface p)) \<and>
      (match_iface (oiface m) (p_oiface p)) \<and>
      (simple_match_ip (src m) (p_src p)) \<and>
      (simple_match_ip (dst m) (p_dst p)) \<and>
      (match_proto (proto m) (p_proto p)) \<and>
      (simple_match_port (sports m) (p_sport p)) \<and>
      (simple_match_port (dports m) (p_dport p))"


  text\<open>The semantics of a simple firewall: just iterate over the rules sequentially\<close>
  fun simple_fw :: "'i::len simple_rule list \<Rightarrow> ('i, 'a) simple_packet_scheme \<Rightarrow> state" where
    "simple_fw [] _ = Undecided" |
    "simple_fw ((SimpleRule m Accept)#rs) p = (if simple_matches m p then Decision FinalAllow else simple_fw rs p)" |
    "simple_fw ((SimpleRule m Drop)#rs) p = (if simple_matches m p then Decision FinalDeny else simple_fw rs p)"
 
  fun simple_fw_alt where
    "simple_fw_alt [] _ = Undecided" |
    "simple_fw_alt (r#rs) p = (if simple_matches (match_sel r) p then 
    	(case action_sel r of Accept \<Rightarrow> Decision FinalAllow | Drop \<Rightarrow> Decision FinalDeny) else simple_fw_alt rs p)"
 
  lemma simple_fw_alt: "simple_fw r p = simple_fw_alt r p" by(induction rule: simple_fw.induct) simp_all

  definition simple_match_any :: "'i::len simple_match" where
    "simple_match_any \<equiv> \<lparr>iiface=ifaceAny, oiface=ifaceAny, src=(0,0), dst=(0,0), proto=ProtoAny, sports=(0,65535), dports=(0,65535) \<rparr>"
  lemma simple_match_any: "simple_matches simple_match_any p"
    proof -
      have "(65535::16 word) = max_word" by(simp add: max_word_def)
      thus ?thesis by(simp add: simple_match_any_def ipset_from_cidr_0 match_ifaceAny)
    qed

  text\<open>we specify only one empty port range\<close>
  definition simple_match_none :: "'i::len simple_match" where
    "simple_match_none \<equiv>
      \<lparr>iiface=ifaceAny, oiface=ifaceAny, src=(1,0), dst=(0,0),
       proto=ProtoAny, sports=(1,0), dports=(0,65535) \<rparr>"
  lemma simple_match_none: "\<not> simple_matches simple_match_none p"
    proof -
      show ?thesis by(simp add: simple_match_none_def)
    qed

  fun empty_match :: "'i::len simple_match \<Rightarrow> bool" where
    "empty_match \<lparr>iiface=_, oiface=_, src=_, dst=_, proto=_,
                  sports=(sps1, sps2), dports=(dps1, dps2) \<rparr> \<longleftrightarrow> (sps1 > sps2) \<or> (dps1 > dps2)"

  lemma empty_match: "empty_match m \<longleftrightarrow> (\<forall>(p::('i::len, 'a) simple_packet_scheme). \<not> simple_matches m p)"
    proof
      assume "empty_match m"
      thus "\<forall>p. \<not> simple_matches m p" by(cases m) fastforce
    next
      assume assm: "\<forall>(p::('i::len, 'a) simple_packet_scheme). \<not> simple_matches m p"
      obtain iif oif sip dip protocol sps1 sps2 dps1 dps2 where m:
        "m = \<lparr>iiface = iif, oiface = oif, src = sip, dst = dip, proto = protocol, sports = (sps1, sps2), dports = (dps1, dps2)\<rparr>"
          by(cases m) force

      show "empty_match m"
        proof(simp add: m)
          let ?x="\<lambda>p. dps1 \<le> p_dport p \<longrightarrow> p_sport p \<le> sps2 \<longrightarrow> sps1 \<le> p_sport p \<longrightarrow> 
              match_proto protocol (p_proto p) \<longrightarrow> simple_match_ip dip (p_dst p) \<longrightarrow> simple_match_ip sip (p_src p) \<longrightarrow>
              match_iface oif (p_oiface p) \<longrightarrow> match_iface iif (p_iiface p) \<longrightarrow> \<not> p_dport p \<le> dps2"
          from assm have nomatch: "\<forall>(p::('i::len, 'a) simple_packet_scheme). ?x p" by(simp add: m)
          { fix ips::"'i::len word \<times> nat"
            have "a \<in> ipset_from_cidr a n" for a::"'i::len word" and n
              using ipset_from_cidr_lowest by auto
            hence "simple_match_ip ips (fst ips)" by(cases ips) simp
          } note ips=this
          have proto: "match_proto protocol (case protocol of ProtoAny \<Rightarrow> TCP | Proto p \<Rightarrow> p)"
            by(simp split: protocol.split)
          { fix ifce
            have " match_iface ifce (iface_sel ifce)"
            by(cases ifce) (simp add: match_iface_refl)
          } note ifaces=this
          { fix p::"('i, 'a) simple_packet_scheme"
            from nomatch have "?x p" by blast
          } note pkt1=this
          obtain p::"('i, 'a) simple_packet_scheme" where [simp]:
			  "p_iiface p = iface_sel iif"
			  "p_oiface p = iface_sel oif"
			  "p_src p = fst sip"
			  "p_dst p = fst dip"
			  "p_proto p = (case protocol of ProtoAny \<Rightarrow> TCP | Proto p \<Rightarrow> p)"
			  "p_sport p = sps1"
			  "p_dport p = dps1"
			  by (meson simple_packet.select_convs)
          note pkt=pkt1[of p, simplified]
          from pkt ips proto ifaces have " sps1 \<le> sps2 \<longrightarrow> \<not> dps1 \<le> dps2" by blast
          thus "sps2 < sps1 \<or> dps2 < dps1" by fastforce
      qed
  qed
    

  lemma nomatch: "\<not> simple_matches m p \<Longrightarrow> simple_fw (SimpleRule m a # rs) p = simple_fw rs p"
    by(cases a, simp_all del: simple_matches.simps)

subsection\<open>Simple Ports\<close>
  fun simpl_ports_conjunct :: "(16 word \<times> 16 word) \<Rightarrow> (16 word \<times> 16 word) \<Rightarrow> (16 word \<times> 16 word)" where
    "simpl_ports_conjunct (p1s, p1e) (p2s, p2e) = (max p1s p2s, min p1e p2e)"

  lemma "{(p1s:: 16 word) .. p1e} \<inter> {p2s .. p2e} = {max p1s p2s .. min p1e p2e}" by(simp)
  
  lemma simple_ports_conjunct_correct:
    "simple_match_port p1 pkt \<and> simple_match_port p2 pkt \<longleftrightarrow> simple_match_port (simpl_ports_conjunct p1 p2) pkt"
    apply(cases p1, cases p2, simp)
    by blast

  lemma simple_match_port_code[code] :"simple_match_port (s,e) p_p = (s \<le> p_p \<and> p_p \<le> e)" by simp

  lemma simple_match_port_UNIV: "{p. simple_match_port (s,e) p} = UNIV \<longleftrightarrow> (s = 0 \<and> e = max_word)"
    apply(simp)
    apply(rule)
     apply(case_tac "s = 0")
      using antisym_conv apply blast
     using word_le_0_iff apply blast
    using word_zero_le by blast

subsection\<open>Simple IPs\<close>
  lemma simple_match_ip_conjunct:
    fixes ip1 :: "'i::len word \<times> nat"
    shows "simple_match_ip ip1 p_ip \<and> simple_match_ip ip2 p_ip \<longleftrightarrow> 
            (case ipcidr_conjunct ip1 ip2 of None \<Rightarrow> False | Some ipx \<Rightarrow> simple_match_ip ipx p_ip)"
  proof -
  {
    fix b1 m1 b2 m2
    have "simple_match_ip (b1, m1) p_ip \<and> simple_match_ip (b2, m2) p_ip \<longleftrightarrow> 
          p_ip \<in> ipset_from_cidr b1 m1 \<inter> ipset_from_cidr b2 m2"
    by simp
    also have "\<dots> \<longleftrightarrow> p_ip \<in> (case ipcidr_conjunct (b1, m1) (b2, m2) of None \<Rightarrow> {} | Some (bx, mx) \<Rightarrow> ipset_from_cidr bx mx)"
      using ipcidr_conjunct_correct by blast
    also have "\<dots> \<longleftrightarrow> (case ipcidr_conjunct (b1, m1) (b2, m2) of None \<Rightarrow> False | Some ipx \<Rightarrow> simple_match_ip ipx p_ip)"
      by(simp split: option.split)
    finally have "simple_match_ip (b1, m1) p_ip \<and> simple_match_ip (b2, m2) p_ip \<longleftrightarrow> 
         (case ipcidr_conjunct (b1, m1) (b2, m2) of None \<Rightarrow> False | Some ipx \<Rightarrow> simple_match_ip ipx p_ip)" .
   } thus ?thesis by(cases ip1, cases ip2, simp)
  qed

  declare simple_matches.simps[simp del]

subsection\<open>Merging Simple Matches\<close>
  text\<open>@{typ "'i::len simple_match"} @{text \<and>} @{typ "'i::len simple_match"}\<close>
  
  fun simple_match_and :: "'i::len simple_match \<Rightarrow> 'i simple_match \<Rightarrow> 'i simple_match option" where
    "simple_match_and \<lparr>iiface=iif1, oiface=oif1, src=sip1, dst=dip1, proto=p1, sports=sps1, dports=dps1 \<rparr> 
                      \<lparr>iiface=iif2, oiface=oif2, src=sip2, dst=dip2, proto=p2, sports=sps2, dports=dps2 \<rparr> = 
      (case ipcidr_conjunct sip1 sip2 of None \<Rightarrow> None | Some sip \<Rightarrow> 
      (case ipcidr_conjunct dip1 dip2 of None \<Rightarrow> None | Some dip \<Rightarrow> 
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
  
      have sip_None: "ipcidr_conjunct sip1 sip2 = None \<Longrightarrow> \<not> simple_match_ip sip1 (p_src p) \<or> \<not> simple_match_ip sip2 (p_src p)"
        using simple_match_ip_conjunct[of sip1 "p_src p" sip2] by simp
      have dip_None: "ipcidr_conjunct dip1 dip2 = None \<Longrightarrow> \<not> simple_match_ip dip1 (p_dst p) \<or> \<not> simple_match_ip dip2 (p_dst p)"
        using simple_match_ip_conjunct[of dip1 "p_dst p" dip2] by simp
      have sip_Some: "\<And>ip. ipcidr_conjunct sip1 sip2 = Some ip \<Longrightarrow>
        simple_match_ip ip (p_src p) \<longleftrightarrow> simple_match_ip sip1 (p_src p) \<and> simple_match_ip sip2 (p_src p)"
        using simple_match_ip_conjunct[of sip1 "p_src p" sip2] by simp
      have dip_Some: "\<And>ip. ipcidr_conjunct dip1 dip2 = Some ip \<Longrightarrow>
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
  
      have case_Some: "\<And>m. Some m = simple_match_and m1 m2 \<Longrightarrow>
       (simple_matches m1 p \<and> simple_matches m2 p) \<longleftrightarrow> simple_matches m p"
       apply(simp add: m1 m2 simple_matches.simps split: option.split_asm)
       using simple_ports_conjunct_correct by(blast dest: sip_Some dip_Some iiface_Some oiface_Some proto_Some)
      have case_None: "simple_match_and m1 m2 = None \<Longrightarrow> \<not> (simple_matches m1 p \<and> simple_matches m2 p)"
       apply(simp add: m1 m2 simple_matches.simps split: option.split_asm)
           apply(blast dest: sip_None dip_None iiface_None oiface_None proto_None)+
       done
      from case_Some case_None show ?thesis by(cases "simple_match_and m1 m2") simp_all
   qed
  
  lemma simple_match_and_SomeD: "simple_match_and m1 m2 = Some m \<Longrightarrow>
    simple_matches m p \<longleftrightarrow> (simple_matches m1 p \<and> simple_matches m2 p)"
    by(simp add: simple_match_and_correct)
  lemma simple_match_and_NoneD: "simple_match_and m1 m2 = None \<Longrightarrow>
    \<not>(simple_matches m1 p \<and> simple_matches m2 p)"
    by(simp add: simple_match_and_correct)
  lemma simple_matches_andD: "simple_matches m1 p \<Longrightarrow> simple_matches m2 p \<Longrightarrow>
    \<exists>m. simple_match_and m1 m2 = Some m \<and> simple_matches m p"
    by (meson option.exhaust_sel simple_match_and_NoneD simple_match_and_SomeD)

subsection\<open>Further Properties of a Simple Firewall\<close>
  fun has_default_policy :: "'i::len simple_rule list \<Rightarrow> bool" where
    "has_default_policy [] = False" |
    "has_default_policy [(SimpleRule m _)] = (m = simple_match_any)" |
    "has_default_policy (_#rs) = has_default_policy rs"
  
  lemma has_default_policy: "has_default_policy rs \<Longrightarrow>
    simple_fw rs p = Decision FinalAllow \<or> simple_fw rs p = Decision FinalDeny"
    proof(induction rs rule: has_default_policy.induct)
    case 1 thus ?case by (simp)
    next
    case (2 m a) thus ?case by(cases a) (simp_all add: simple_match_any)
    next
    case (3 r1 r2 rs)
      from 3 obtain a m where "r1 = SimpleRule m a" by (cases r1) simp
      with 3 show ?case by (cases a) simp_all
    qed
  
  lemma has_default_policy_fst: "has_default_policy rs \<Longrightarrow> has_default_policy (r#rs)"
   apply(cases r, rename_tac m a, simp)
   apply(cases rs)
    by(simp_all)


  text\<open>We can stop after a default rule (a rule which matches anything) is observed.\<close>
  fun cut_off_after_match_any :: "'i::len simple_rule list \<Rightarrow> 'i simple_rule list" where
    "cut_off_after_match_any [] = []" |
    "cut_off_after_match_any (SimpleRule m a # rs) =
      (if m = simple_match_any then [SimpleRule m a] else SimpleRule m a # cut_off_after_match_any rs)"
  
  lemma cut_off_after_match_any: "simple_fw (cut_off_after_match_any rs) p = simple_fw rs p"
    apply(induction rs p rule: simple_fw.induct)
      by(simp add: simple_match_any)+
  
  lemma simple_fw_not_matches_removeAll: "\<not> simple_matches m p \<Longrightarrow>
    simple_fw (removeAll (SimpleRule m a) rs) p = simple_fw rs p"
    apply(induction rs p rule: simple_fw.induct)
      apply(simp)
     apply(simp_all)
     apply blast+
    done


subsection\<open>Reality check: Validity of Simple Matches\<close>
  text\<open>While it is possible to construct a @{text "simple_fw"} expression that only matches a source
  or destination port, such a match is not meaningful, as the presence of the port information is 
  dependent on the protocol. Thus, a match for a port should always include the match for a protocol.
  Additionally, prefixes should be zero on bits beyond the prefix length.
  \<close>
  
  definition "valid_prefix_fw m = valid_prefix (uncurry PrefixMatch m)"
  
  lemma ipcidr_conjunct_valid:
    "\<lbrakk>valid_prefix_fw p1; valid_prefix_fw p2; ipcidr_conjunct p1 p2 = Some p\<rbrakk> \<Longrightarrow> valid_prefix_fw p"
    unfolding valid_prefix_fw_def
    by(cases p; cases p1; cases p2) (simp add: ipcidr_conjunct.simps split: if_splits)
  
  definition simple_match_valid :: "('i::len, 'a) simple_match_scheme \<Rightarrow> bool" where
    "simple_match_valid m \<equiv> 
    ({p. simple_match_port (sports m) p} \<noteq> UNIV \<or> {p. simple_match_port (dports m) p} \<noteq> UNIV \<longrightarrow>
        proto m \<in> Proto `{TCP, UDP, L4_Protocol.SCTP}) \<and>
    valid_prefix_fw (src m) \<and> valid_prefix_fw (dst m)" 
  
  lemma simple_match_valid_alt[code_unfold]: "simple_match_valid = (\<lambda> m.
    (let c = (\<lambda>(s,e). (s \<noteq> 0 \<or> e \<noteq> max_word)) in (
    if c (sports m) \<or> c (dports m) then proto m = Proto TCP \<or> proto m = Proto UDP \<or> proto m = Proto L4_Protocol.SCTP else True)) \<and>
  valid_prefix_fw (src m) \<and> valid_prefix_fw (dst m))" 
  proof -
    have simple_match_valid_alt_hlp1: "{p. simple_match_port x p} \<noteq> UNIV \<longleftrightarrow> (case x of (s,e) \<Rightarrow> s \<noteq> 0 \<or> e \<noteq> max_word)"
      for x using simple_match_port_UNIV by auto
    have simple_match_valid_alt_hlp2: "{p. simple_match_port x p} \<noteq> {} \<longleftrightarrow> (case x of (s,e) \<Rightarrow> s \<le> e)" for x by auto
    show ?thesis
      unfolding fun_eq_iff
      unfolding simple_match_valid_def Let_def
      unfolding simple_match_valid_alt_hlp1 simple_match_valid_alt_hlp2
      apply(clarify, rename_tac m, case_tac "sports m"; case_tac "dports m"; case_tac "proto m")
       by auto
  qed
  
  text\<open>Example:\<close>
  context
  begin
    private definition "example_simple_match1 \<equiv>
      \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', src = (0::32 word, 0), dst = (0, 0),
       proto = Proto TCP, sports = (0, 1024), dports = (0, 1024)\<rparr>"
  
    lemma "simple_fw [SimpleRule example_simple_match1 Drop]
      \<lparr>p_iiface = '''', p_oiface = '''',  p_src = (1::32 word), p_dst = 2, p_proto = TCP, p_sport = 8,
       p_dport = 9, p_tcp_flags = {}, p_payload = ''''\<rparr> =
        Decision FinalDeny" by eval
  
    private definition "example_simple_match2 \<equiv> example_simple_match1\<lparr> proto := ProtoAny \<rparr>"
    text\<open>Thus, @{text "example_simple_match1"} is valid, but if we set its protocol match to any, it isn't anymore\<close>
    private lemma "simple_match_valid example_simple_match1" by eval
    private lemma "\<not> simple_match_valid example_simple_match2" by eval
  end
  
  
  lemma simple_match_and_valid: 
    fixes m1 :: "'i::len simple_match"
    assumes mv: "simple_match_valid m1" "simple_match_valid m2"
    assumes mj: "simple_match_and m1 m2 = Some m"
    shows "simple_match_valid m"
  proof -
    have simpl_ports_conjunct_not_UNIV:
    "Collect (simple_match_port x) \<noteq> UNIV \<Longrightarrow>
      x = simpl_ports_conjunct p1 p2 \<Longrightarrow>
      Collect (simple_match_port p1) \<noteq> UNIV \<or> Collect (simple_match_port p2) \<noteq> UNIV" 
    for x p1 p2 by (metis Collect_cong mem_Collect_eq simple_ports_conjunct_correct)
  
    (* prefix validity. That's simple. *)
    have "valid_prefix_fw (src m1)" "valid_prefix_fw (src m2)" "valid_prefix_fw (dst m1)" "valid_prefix_fw (dst m2)"
      using mv unfolding simple_match_valid_alt by simp_all
    moreover have "ipcidr_conjunct (src m1) (src m2) = Some (src m)"
                  "ipcidr_conjunct (dst m1) (dst m2) = Some (dst m)"
      using mj by(cases m1; cases m2; cases m; simp split: option.splits)+
    ultimately have pv: "valid_prefix_fw (src m)" "valid_prefix_fw (dst m)"
      using ipcidr_conjunct_valid by blast+
  
    (* now for the source ports\<dots> *)
    def nmu \<equiv> "\<lambda>ps. {p. simple_match_port ps p} \<noteq> UNIV"
    have "simpl_ports_conjunct (sports m1) (sports m2) = (sports m)" (is "?ph1 sports")
      using mj by(cases m1; cases m2; cases m; simp split: option.splits)
    hence sp: "nmu (sports m) \<longrightarrow> nmu (sports m1) \<or> nmu (sports m2)"
      (is "?ph2 sports")
      unfolding nmu_def using simpl_ports_conjunct_not_UNIV by metis
  
    (* dst ports: mutatis mutandem *)
    have "?ph1 dports" using mj by(cases m1; cases m2; cases m; simp split: option.splits)
    hence dp: "?ph2 dports" unfolding nmu_def using simpl_ports_conjunct_not_UNIV by metis
  
    (* And an argument for the protocol. *)
    def php \<equiv> "\<lambda>mr :: 'i simple_match. proto mr \<in> Proto ` {TCP, UDP, L4_Protocol.SCTP}"
    have pcj: "simple_proto_conjunct (proto m1) (proto m2) = Some (proto m)"
      using mj by(cases m1; cases m2; cases m; simp split: option.splits)
    hence p: "php m1 \<Longrightarrow> php m"
             "php m2 \<Longrightarrow> php m"
      using conjunctProtoD conjunctProtoD2 pcj unfolding php_def by auto
  
    (* Since I'm trying to trick the simplifier with these defs, I need these as explicit statements: *)
    have "\<And>mx. simple_match_valid mx \<Longrightarrow> nmu (sports mx) \<or> nmu (dports mx) \<Longrightarrow> php mx"
      unfolding nmu_def php_def simple_match_valid_def by blast
    hence mps: "nmu (sports m1) \<Longrightarrow> php m1" "nmu (dports m1) \<Longrightarrow> php m1"
               "nmu (sports m2) \<Longrightarrow> php m2" "nmu (dports m2) \<Longrightarrow> php m2" using mv by blast+
    
    have pa: "nmu (sports m) \<or> nmu (dports m) \<longrightarrow> php m"
    (*  apply(intro impI)
      apply(elim disjE)
      apply(drule sp[THEN mp])
      apply(elim disjE)
      apply(drule mps)
      apply(elim p; fail) *)
      using sp dp mps p by fast
  
    show ?thesis
      unfolding simple_match_valid_def
      using pv pa[unfolded nmu_def php_def] by blast
  qed
      
  
  definition "simple_fw_valid \<equiv> list_all (simple_match_valid \<circ> match_sel)"

end

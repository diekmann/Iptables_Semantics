theory SimpleFw_Semantics
imports Main "../Common/Negation_Type"
  "../Firewall_Common_Decision_State"
  "../Primitive_Matchers/IpAddresses"
  "../Primitive_Matchers/Iface"
  "../Primitive_Matchers/Protocol"
  "../Primitive_Matchers/Simple_Packet"
begin


section{*Simple Firewall Syntax (IPv4 only)*}


  datatype simple_action = Accept | Drop
  
  text{*Simple match expressions do not allow negated expressions.
        However, Most match expressions can still be transformed into simple match expressions.
        
        A negated IP address range can be represented as a set of non-negated IP ranges.
        For example @{text "!8 = {0..7} \<union> {8 .. ipv4max}"}.
        Using CIDR notation (i.e. the @{text "a.b.c.d/n"} notation), we can represent negated IP
        ranges as a set of non-negated IP ranges with only fair blowup.
        Another handy result is that the conjunction of two IP ranges in CIDR notation is 
        either the smaller of the two ranges or the empty set.
        An empty IP range cannot be represented.
        If one wants to represent the empty range, then the complete rule needs to be removed.

        The same holds for layer 4 ports.
        In addition, there exists an empty port range, e.g. @{text "(1,0)"}.
        The conjunction of two port ranges is again just one port range.
        
        But negation of interfaces is not supported. Since interfaces support a wildcard character,
        transforming a negated interface would either result in an infeasible blowup or requires
        knowledge about the existing interfaces (e.g. there only is eth0, eth1, wlan3, and vbox42)
        An empirical test shows that negated interfaces do not occur in our data sets.
        Negated interfaces can also be considered bad style: What is !eth0? Everything that is
        not eth0, experience shows that interfaces may come up randomly, in particular in combination 
        with virtual machines, so !eth0 might not be the desired match.
        At the moment, if an negated interface occurs which prevents translation to a simple match,
        we recommend to abstract the negated interface to unknown and remove it (upper or lower closure
        rule set) before translating to a simple match.
        The same discussion holds for negated protocols.

        Noteworthy, simple match expressions are both expressive and support conjunction:
        @{text "simple-match1 \<and> simple-match2 = simple-match3"}
        *}
        (*It took very long to design the simple match such that it can represent everything we need
        and that you can calculate with it. Disjunction is easy: just have two consecutive rules with the same action.
        Conjunction was a tough fight! It is needed to translate:
        common_primitive_match_to_simple_match (MatchAny e1 e2) =
          simple_match_and (common_primitive_match_to_simple_match e1) (common_primitive_match_to_simple_match e2)
        This is key to translate common_primitive_match to simple_match

        It may seem a simple enhancement to support iiface :: "iface negation_type", but then you
        can no longer for the conjunction of two simple_matches.
        *)

  record 'i simple_match =
    iiface :: "iface" --"in-interface"
      (*we cannot (and don't want to, c.f. git history) express negated interfaces*)
      (*We could also drop interface wildcard support and try negated interfaces again \<dots>*)
    oiface :: "iface" --"out-interface"
    src :: "('i::len word \<times> nat) " --"source IP address"
    dst :: "('i::len word \<times> nat) " --"destination"
    proto :: "protocol"
    sports :: "(16 word \<times> 16 word)" --"source-port first:last"
    dports :: "(16 word \<times> 16 word)" --"destination-port first:last"


  datatype 'i simple_rule = SimpleRule (match_sel: "'i simple_match") (action_sel: simple_action)

subsection{*Simple Firewall Semantics*}


  (*Sanity check:*)
  lemma "ipset_from_cidr = ipv4range_set_from_prefix"
    by(simp add: fun_eq_iff ipset_from_cidr_def ipv4range_set_from_prefix_alt1 ipset_from_netmask_def ipv4range_set_from_netmask_def)

  fun simple_match_ip :: "('i::len word \<times> nat) \<Rightarrow> 'i::len word \<Rightarrow> bool" where
    "simple_match_ip (base, len) p_ip \<longleftrightarrow> p_ip \<in> ipset_from_cidr base len"

  (*TODO: move?*)
  fun simple_match_ip4 :: "(ipv4addr \<times> nat) \<Rightarrow> ipv4addr \<Rightarrow> bool" where
    "simple_match_ip4 (base, len) p_ip \<longleftrightarrow> p_ip \<in> ipv4range_set_from_prefix base len"

  lemma wordinterval_to_set_ipv4_cidr_tuple_to_interval_simple_match_ip_set:
    "wordinterval_to_set (ipv4_cidr_tuple_to_interval ip) = {d. simple_match_ip4 ip d}"
    proof -
      { fix s d
        from ipv4range_to_set_def wordinterval_to_set_ipv4_cidr_tuple_to_interval have
          "s \<in> wordinterval_to_set (ipv4_cidr_tuple_to_interval d) \<longleftrightarrow> simple_match_ip4 d s"
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


  text{*The semantics of a simple firewall: just iterate over the rules sequentially*}
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

  text{*we specify only one empty port range*}
  definition simple_match_none :: "'i::len simple_match" where
    "simple_match_none \<equiv> \<lparr>iiface=ifaceAny, oiface=ifaceAny, src=(1,0), dst=(0,0), proto=ProtoAny, sports=(1,0), dports=(0,65535) \<rparr>"
  lemma simple_match_none: "\<not> simple_matches simple_match_none p"
    proof -
      show ?thesis by(simp add: simple_match_none_def)
    qed

  fun empty_match :: "'i::len simple_match \<Rightarrow> bool" where
    "empty_match \<lparr>iiface=_, oiface=_, src=_, dst=_, proto=_, sports=(sps1, sps2), dports=(dps1, dps2) \<rparr> \<longleftrightarrow> (sps1 > sps2) \<or> (dps1 > dps2)"

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
              apply(simp add: ipset_from_cidr_def)
            using ipv4range_set_from_prefix_eq_ip4_set sorry (* by blast (*TODO*)*)
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
    

subsection{*Simple Ports*}
  fun simpl_ports_conjunct :: "(16 word \<times> 16 word) \<Rightarrow> (16 word \<times> 16 word) \<Rightarrow> (16 word \<times> 16 word)" where
    "simpl_ports_conjunct (p1s, p1e) (p2s, p2e) = (max p1s p2s, min p1e p2e)"

  lemma "{(p1s:: 16 word) .. p1e} \<inter> {p2s .. p2e} = {max p1s p2s .. min p1e p2e}" by(simp)
  
  lemma simple_ports_conjunct_correct: "simple_match_port p1 pkt \<and> simple_match_port p2 pkt \<longleftrightarrow> simple_match_port (simpl_ports_conjunct p1 p2) pkt"
    apply(cases p1, cases p2, simp)
    by blast

  lemma simple_match_port_code[code] :"simple_match_port (s,e) p_p = (s \<le> p_p \<and> p_p \<le> e)" by simp

  (*lemma simple_match_port_wordinterval: "simple_match_port (s,e) p \<longleftrightarrow> p \<in> wordinterval_to_set (WordInterval s e)" by(simp)*)

  fun simple_match_port_and_not :: "(16 word \<times> 16 word) \<Rightarrow> (16 word \<times> 16 word) \<Rightarrow> ((16 word \<times> 16 word) \<times> (16 word \<times> 16 word) option) option" where
    "simple_match_port_and_not (s, e) (s_n, e_n) = (let w = wordinterval_setminus (WordInterval s e) (WordInterval s_n e_n) in 
      (if wordinterval_empty w then None
       else case w of WordInterval s' e' \<Rightarrow> Some ((s', e'), None) (*optimized wordintervals don't have overlapping intervals*)
                   |  _ \<Rightarrow> Some ((s,e), Some (s_n, e_n)))
      )"

  lemma "simple_match_port_and_not p1 p2 = Some (p_p, Some p_n) \<Longrightarrow>
    simple_match_port p1 p \<and> \<not> simple_match_port p2 p \<longleftrightarrow> simple_match_port p_p p \<and> \<not> simple_match_port p_n p"
    apply(cases p1, cases p2, cases p_p, cases p_n)
    by(simp split:split_if_asm wordinterval.split_asm)
  lemma "simple_match_port_and_not p1 p2 = None \<Longrightarrow> \<not>(\<exists>p. simple_match_port p1 p \<and> \<not> simple_match_port p2 p)"
    apply(cases p1, cases p2)
    apply(simp split:split_if_asm wordinterval.split_asm)
    by fastforce
  lemma "simple_match_port_and_not p1 p2 = Some (p_p, None) \<Longrightarrow>
    simple_match_port p1 p \<and> \<not> simple_match_port p2 p \<longleftrightarrow> simple_match_port p_p p"
  proof(cases p1, cases p2, cases p_p, simp split:split_if_asm wordinterval.split_asm)
   fix s1::"16 word" and e1 s2 e2 sp ep
   assume 1: "wordinterval_setminus (WordInterval s1 e1) (WordInterval s2 e2) = WordInterval sp ep"
   from 1 have "wordinterval_to_set (wordinterval_setminus (WordInterval s1 e1) (WordInterval s2 e2)) = wordinterval_to_set (WordInterval sp ep)"
     by simp
   hence "{s1..e1} - {s2..e2} = {sp..ep}" using wordinterval_setminus_set_eq by simp
   thus "(s1 \<le> p \<and> p \<le> e1 \<and> (s2 \<le> p \<longrightarrow> \<not> p \<le> e2)) = (sp \<le> p \<and> p \<le> ep)" by auto
  qed

  value[code] "simple_match_port_and_not (1,8) (6,8)"

subsection{*Simple IPs*}
  lemma simple_match_ip_conjunct: "simple_match_ip ip1 p_ip \<and> simple_match_ip ip2 p_ip \<longleftrightarrow> 
         (case ipv4cidr_conjunct ip1 ip2 of None \<Rightarrow> False | Some ipx \<Rightarrow> simple_match_ip ipx p_ip)"
  proof -
  {
    fix b1 m1 b2 m2
    have "simple_match_ip (b1, m1) p_ip \<and> simple_match_ip (b2, m2) p_ip \<longleftrightarrow> 
          p_ip \<in> ipset_from_cidr b1 m1 \<inter> ipset_from_cidr b2 m2"
    by simp
    also have "\<dots> \<longleftrightarrow> p_ip \<in> (case ipv4cidr_conjunct (b1, m1) (b2, m2) of None \<Rightarrow> {} | Some (bx, mx) \<Rightarrow> ipv4range_set_from_prefix bx mx)"
      using ipv4cidr_conjunct_correct (*by blast*) sorry
    also have "\<dots> \<longleftrightarrow> (case ipv4cidr_conjunct (b1, m1) (b2, m2) of None \<Rightarrow> False | Some ipx \<Rightarrow> simple_match_ip ipx p_ip)"
      by(simp split: option.split)
    finally have "simple_match_ip (b1, m1) p_ip \<and> simple_match_ip (b2, m2) p_ip \<longleftrightarrow> 
         (case ipv4cidr_conjunct (b1, m1) (b2, m2) of None \<Rightarrow> False | Some ipx \<Rightarrow> simple_match_ip ipx p_ip)" .
   } thus ?thesis by(cases ip1, cases ip2, simp)
  qed


declare simple_matches.simps[simp del]

subsubsection{*Merging Simple Matches*}
text{*@{typ "'i::len simple_match"} @{text \<and>} @{typ "'i::len simple_match"}*}

fun simple_match_and :: "'i::len simple_match \<Rightarrow> 'i simple_match \<Rightarrow> 'i simple_match option" where
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

lemma simple_match_and_SomeD: "simple_match_and m1 m2 = Some m \<Longrightarrow> simple_matches m p = (simple_matches m1 p \<and> simple_matches m2 p)"
	by(simp add: simple_match_and_correct)
lemma simple_match_and_NoneD: "simple_match_and m1 m2 = None \<Longrightarrow> \<not>(simple_matches m1 p \<and> simple_matches m2 p)"
	by(simp add: simple_match_and_correct)
lemma simple_matches_andD: "simple_matches m1 p \<Longrightarrow> simple_matches m2 p \<Longrightarrow> \<exists>m. simple_match_and m1 m2 = Some m \<and> simple_matches m p"
  by (meson option.exhaust_sel simple_match_and_NoneD simple_match_and_SomeD)

(*
(*TODO*)
  context begin
  (*TODO*)
  (*if we had a quite optimized version of this, ...*)
  (*positive match \<times> negative match*)
  private fun simple_match_and_not :: "simple_match \<Rightarrow> simple_match \<Rightarrow> (simple_match \<times> simple_match option) option" where
    "simple_match_and_not pos neg = 
      Some (pos, Some neg)"

  lemma "simple_match_and_not m1 m2 = Some (m_p, Some m_n) \<Longrightarrow>
    simple_matches m1 p \<and> \<not> simple_matches m2 p \<longleftrightarrow> simple_matches m_p p \<and> \<not> simple_matches m_n p"
  apply(cases m1, cases m2)
  by(simp)
  lemma "simple_match_and_not m1 m2 = None \<Longrightarrow> \<not>(\<exists>p. simple_matches m1 p \<and> \<not> simple_matches m2 p)"
  apply(cases m1, cases m2)
  by(simp)
  lemma "simple_match_and_not m1 m2 = Some (m_p, None) \<Longrightarrow>
    simple_matches m1 p \<and> \<not> simple_matches m2 p \<longleftrightarrow> simple_matches m_p p"
  apply(cases m1, cases m2)
  by(simp)
end
(*END TODO*)
*)

lemma nomatch: "\<not> simple_matches m p \<Longrightarrow> simple_fw (SimpleRule m a # rs) p = simple_fw rs p"
  by(cases a, simp_all)



definition "example_simple_match1 \<equiv> \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', src = (0, 0), dst = (0, 0), proto = Proto TCP, sports = (0, 0x0), dports = (0, 0x0)\<rparr>"
(*export_code simple_fw in SML   not possible here*)
value[code] "simple_fw [
  SimpleRule example_simple_match1 simple_action.Drop]
  
  \<lparr>p_iiface = '''', p_oiface = '''',  p_src = 1, p_dst = 2, p_proto = TCP, p_sport = 8, p_dport = 9, p_tcp_flags = {}, p_tag_ctstate = CT_New\<rparr>"

fun has_default_policy :: "simple_rule list \<Rightarrow> bool" where
  "has_default_policy [] = False" |
  "has_default_policy [(SimpleRule m _)] = (m = simple_match_any)" |
  "has_default_policy (_#rs) = has_default_policy rs"

lemma has_default_policy: "has_default_policy rs \<Longrightarrow> simple_fw rs p = Decision FinalAllow \<or> simple_fw rs p = Decision FinalDeny"
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




lemma simple_fw_not_matches_removeAll: "\<not> simple_matches m p \<Longrightarrow> simple_fw (removeAll (SimpleRule m a) rs) p = simple_fw rs p"
  apply(induction rs p rule: simple_fw.induct)
    apply(simp)
   apply(simp_all)
   apply blast+
  done

subsection{*Reality check*}
text{* While it is possible to construct a @{text "simple_fw"} expression that only matches a source
or destination port, such a match is not meaningful, as the presence of the port information is 
dependent on the protocol. Thus, a match for a port should always include the match for a protocol.
Additionally, prefixes should be zero on bits beyond the prefix length.
*}

definition "valid_prefix_fw m = valid_prefix (split PrefixMatch m)"

definition "simple_match_valid m \<equiv> 
(((({p. simple_match_port (sports m) p} \<noteq> UNIV (*\<and> {p. simple_match_port (sports m) p} \<noteq> {}*)) \<or> 
({p. simple_match_port (dports m) p} \<noteq> UNIV (*\<and> {p. simple_match_port (dports m) p} \<noteq> {}*))) 
\<longrightarrow> (proto m \<in> Proto `{TCP, UDP, SCTP})) \<and>
valid_prefix_fw (src m) \<and> valid_prefix_fw (dst m)
)" 

lemma simple_match_valid_alt_hlp1: "{p. simple_match_port x p} \<noteq> UNIV \<longleftrightarrow> (case x of (s,e) \<Rightarrow> s \<noteq> 0 \<or> e \<noteq> max_word)"
	apply(clarsimp simp: set_eq_UNIV split: prod.splits)
	apply(auto)
	 using word_le_0_iff apply blast
	using antisym_conv apply blast
done
lemma simple_match_valid_alt_hlp2: "{p. simple_match_port x p} \<noteq> {} \<longleftrightarrow> (case x of (s,e) \<Rightarrow> s \<le> e)" by auto
lemma simple_match_valid_alt[code_unfold]: "simple_match_valid = (\<lambda> m.
	(let c = (\<lambda>(s,e). (*s \<le> e \<and>*) (s \<noteq> 0 \<or> e \<noteq> max_word)) in (
	if c (sports m) \<or> c (dports m) then proto m = Proto TCP \<or> proto m = Proto UDP \<or> proto m = Proto SCTP else True)) \<and>
valid_prefix_fw (src m) \<and> valid_prefix_fw (dst m))
" 
unfolding fun_eq_iff
unfolding simple_match_valid_def Let_def
unfolding simple_match_valid_alt_hlp1 simple_match_valid_alt_hlp2
by(clarify, rename_tac m, case_tac "sports m"; case_tac "dports m"; case_tac "proto m") auto

definition "example_simple_match2 \<equiv> (proto_update (const ProtoAny) example_simple_match1)"
text{* Thus, @{text "example_simple_match1"} is valid, but if we set its protocol match to any, it no longer is. *}
lemma "simple_match_valid example_simple_match1" by eval
lemma "\<not>simple_match_valid example_simple_match2" by eval

definition "simple_fw_valid \<equiv> list_all (simple_match_valid \<circ> match_sel)"

end

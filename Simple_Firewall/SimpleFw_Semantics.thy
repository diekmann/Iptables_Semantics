theory SimpleFw_Semantics
imports Main "../Bitmagic/IPv4Addr" "../Bitmagic/BitrangeLists" "../Output_Format/Negation_Type"
  "../Firewall_Common_Decision_State"
  "../Primitive_Matchers/Iface"
  "../Primitive_Matchers/Protocol"
  "../Primitive_Matchers/Simple_Packet"
  "../Output_Format/IPSpace_Operations"
begin


section{*Simple Firewall Syntax (IPv4)*}
text{*Very TODO*}
(*TODO*)


  datatype simple_action = Accept | Drop
  
  (*TODO: can we get rid of the negation types?*)
  record simple_match =
    iiface :: "iface" --"in-interface" (*TODO: we cannot (and don't want to, see history) express negated interfaces*)
    oiface :: "iface" --"out-interface"
    src :: "(ipv4addr \<times> ipv4addr) " --"source IP address (start, end) inclusive" (*TODO: 
      for reference, the commit where the negation type was removed is 823703ceb9363deb60ecd4923c39ea6c8901f368
      the last commit with CIDR notation was 0969c2f99afefb316e4f279863b717fd40e0923c*)
    dst :: "(ipv4addr \<times> ipv4addr) " --"destination"
    proto :: "protocol"
    sports :: "(16 word \<times> 16 word)" --"source-port first:last"
    dports :: "(16 word \<times> 16 word)" --"destination-port first:last"
    (*ports have no negation type as this can be represented by multiple firewall rules
      for example: !(3,4)
      is representable by
      (1,2) and (4,65535)
      *)

(*
(*scratch: testing ip range normalize*)
(*TODO move:*)
 lemma "- {4::nat .. 8::nat} = {0..3} \<union> {9..}" by force

 (*hardly expressible with ip/n syntax*)
 lemma "(- (ipv4range_set_from_bitmask 0x11330000 16)) = {0 .. 0x1132FFFF} \<union> {0x11340000 ..}"
   apply(simp add: ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def)
   apply(rule)
    apply(rule)
    apply(simp add: not_le less_le)
    apply(elim disjE conjE)
     apply(simp_all)
     apply(unat_arith)
    apply(unat_arith)
   apply(rule)
    apply(rule)
    apply(simp)
    apply(unat_arith)+
   done
(*hmm, ip range normalizing with these types will result in a horrible blowup
 we probably need the negation types again
  we could show that Neg corresponds to an inverse bitmask, something like the cisco stuff

 we cannot simply merge two Negs, see below

 do we want some ranges like in the ports?
  but translating back an arbitrary range to the syntax used in the (complex) match_expr will get hard
  {a..b} can be translated into b - a single ips (easy)
  optimize (needed!):
    compress to one large ip range and then add a bunch of single ips
    oh boy, this is gonna be some work to do!
  downside: not possible to print it back directly to CIDR notation
  but we need cidr notation!
  so, the optimized {a..b} to [IP x, IP y, foo/n, IP z] must be really good
  and we need a print function then
    print {a..a} \<rightarrow> a
    print {a..b} \<rightarrow> base/mask
       base is longest prefix of a and b appended with zeros, mask is the length of the prefix
    all other ways to store an ip range (i.e. we cannot directly translate it to CIDR notation) must be normalized away (splitting rules)
  the longest prefix CIDR stuff is an optimization we may skip for now
*)
(*end: scratch: testing ip range normalize*)
*)

  datatype simple_rule = SimpleRule simple_match simple_action

subsection{*Simple Firewall Semantics*}

  fun simple_match_ip :: "(ipv4addr \<times> ipv4addr) \<Rightarrow> ipv4addr \<Rightarrow> bool" where
    "simple_match_ip (start, end) p_ip \<longleftrightarrow> p_ip \<in> {start .. end}"

  --"by the way, the words do not wrap around"
  lemma "{(253::8 word) .. 8} = {}" by simp 

  fun simple_match_port :: "(16 word \<times> 16 word) \<Rightarrow> 16 word \<Rightarrow> bool" where
    "simple_match_port (s,e) p_p \<longleftrightarrow> p_p \<in> {s..e}"

  fun simple_matches :: "simple_match \<Rightarrow> simple_packet \<Rightarrow> bool" where
    "simple_matches m p \<longleftrightarrow>
      (match_iface (iiface m) (p_iiface p)) \<and>
      (match_iface (oiface m) (p_oiface p)) \<and>
      (simple_match_ip (src m) (p_src p)) \<and>
      (simple_match_ip (dst m) (p_dst p)) \<and>
      (match_proto (proto m) (p_proto p)) \<and>
      (simple_match_port (sports m) (p_sport p)) \<and>
      (simple_match_port (dports m) (p_dport p))"

  fun simple_fw :: "simple_rule list \<Rightarrow> simple_packet \<Rightarrow> state" where
    "simple_fw [] _ = Undecided" |
    "simple_fw ((SimpleRule m Accept)#rs) p = (if simple_matches m p then Decision FinalAllow else simple_fw rs p)" |
    "simple_fw ((SimpleRule m Drop)#rs) p = (if simple_matches m p then Decision FinalDeny else simple_fw rs p)"



  definition simple_match_any :: "simple_match" where
    "simple_match_any \<equiv> \<lparr>iiface=IfaceAny, oiface=IfaceAny, src=(0,max_ipv4_addr), dst=(0,max_ipv4_addr), proto=ProtoAny, sports=(0,65535), dports=(0,65535) \<rparr>"

  lemma simple_match_any: "simple_matches simple_match_any p"
    apply(simp add: simple_match_any_def ipv4range_set_from_bitmask_0)
    apply(subgoal_tac "(65535::16 word) = max_word")
     apply(simp add: match_IfaceAny)
    apply(simp add: max_word_def)
    done


subsection{*Simple Ports*}
  fun simpl_ports_conjunct :: "(16 word \<times> 16 word) \<Rightarrow> (16 word \<times> 16 word) \<Rightarrow> (16 word \<times> 16 word)" where
    "simpl_ports_conjunct (p1s, p1e) (p2s, p2e) = (max p1s p2s, min p1e p2e)"

  lemma "{(p1s:: 16 word) .. p1e} \<inter> {p2s .. p2e} = {max p1s p2s .. min p1e p2e}" by(simp)
  
  lemma simpl_ports_conjunct_correct: "simple_match_port p1 pkt \<and> simple_match_port p2 pkt \<longleftrightarrow> simple_match_port (simpl_ports_conjunct p1 p2) pkt"
    apply(cases p1, cases p2, simp)
    by blast

subsection{*Simple IPs*}
  (*conjunction of two negations? PROBLEM*)

  (*! !PROBLEM ! !*)

  lemma simple_match_ip_conjunct: "simple_match_ip ip1 p_ip \<and> simple_match_ip ip2 p_ip \<longleftrightarrow> 
         (case simple_ips_conjunct ip1 ip2 of None \<Rightarrow> False | Some ipx \<Rightarrow> simple_match_ip ipx p_ip)"
  proof -
  {
    fix b1 m1 b2 m2
    have "simple_match_ip (b1, m1) p_ip \<and> simple_match_ip (b2, m2) p_ip \<longleftrightarrow> 
          p_ip \<in> ipv4range_set_from_bitmask b1 m1 \<inter> ipv4range_set_from_bitmask b2 m2"
    by simp
    also have "\<dots> \<longleftrightarrow> p_ip \<in> (case simple_ips_conjunct (b1, m1) (b2, m2) of None \<Rightarrow> {} | Some (bx, mx) \<Rightarrow> ipv4range_set_from_bitmask bx mx)"
      using simple_ips_conjunct_correct by blast
    also have "\<dots> \<longleftrightarrow> (case simple_ips_conjunct (b1, m1) (b2, m2) of None \<Rightarrow> False | Some ipx \<Rightarrow> simple_match_ip ipx p_ip)"
      by(simp split: option.split)
    finally have "simple_match_ip (b1, m1) p_ip \<and> simple_match_ip (b2, m2) p_ip \<longleftrightarrow> 
         (case simple_ips_conjunct (b1, m1) (b2, m2) of None \<Rightarrow> False | Some ipx \<Rightarrow> simple_match_ip ipx p_ip)" .
   } thus ?thesis by(cases ip1, cases ip2, simp)
  qed

end

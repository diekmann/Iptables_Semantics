theory SimpleFwSyntax                                                                                                             
imports Main "../Bitmagic/IPv4Addr" "../Bitmagic/BitrangeLists" "../Output_Format/Negation_Type" "../Firewall_Common_Decision_State" "../Primitive_Matchers/Iface"
begin


  datatype primitive_protocol = TCP | UDP | ICMP

section{*Simple Packet*}
  text{*Packet constants are prefixed with p_*}
  record simple_packet = p_iiface :: string
                         p_oiface :: string
                         p_src :: ipv4addr
                         p_dst :: ipv4addr
                         p_proto :: primitive_protocol
                         p_sport :: "16 word"
                         p_dport :: "16 word"

section{*Simple Firewall Syntax (IPv4)*}
  datatype protocol = ProtoAny | Proto "primitive_protocol negation_type"

  
  datatype simple_action = Accept | Drop
  
  (*TODO: can we get rid of the negation types? Or at least at the ports?*)
  record simple_match =
    iiface :: "iface" --"in-interface"
    oiface :: "iface" --"out-interface"
    src :: "(ipv4addr \<times> nat) negation_type" --"source"
    dst :: "(ipv4addr \<times> nat) negation_type" --"destination"
    proto :: "protocol"
    sports :: "(16 word \<times> 16 word) negation_type" --"source-port first:last"
    dports :: "(16 word \<times> 16 word) negation_type" --"destination-port first:last"

  datatype simple_rule = SimpleRule simple_match simple_action

section{*Simple Firewall Semantics*}

  fun simple_match_ip :: "(ipv4addr \<times> nat) negation_type \<Rightarrow> ipv4addr \<Rightarrow> bool" where
    "simple_match_ip (Pos (ip, n)) p_ip \<longleftrightarrow> p_ip \<in> ipv4range_set_from_bitmask ip n" |
    "simple_match_ip (Neg (ip, n)) p_ip \<longleftrightarrow> p_ip \<notin> ipv4range_set_from_bitmask ip n"

  fun simple_match_proto :: "protocol \<Rightarrow> primitive_protocol \<Rightarrow> bool" where
    "simple_match_proto ProtoAny _ \<longleftrightarrow> True" |
    "simple_match_proto (Proto (Pos p)) p_p \<longleftrightarrow> p_p = p" |
    "simple_match_proto (Proto (Neg p)) p_p \<longleftrightarrow> p_p \<noteq> p"

  fun simple_match_port :: "(16 word \<times> 16 word) negation_type \<Rightarrow> 16 word \<Rightarrow> bool" where
    "simple_match_port (Pos (s,e)) p_p \<longleftrightarrow> p_p \<in> {s..e}" |
    "simple_match_port (Neg (s,e)) p_p \<longleftrightarrow> p_p \<notin> {s..e}"

  fun simple_matches :: "simple_match \<Rightarrow> simple_packet \<Rightarrow> bool" where
    "simple_matches m p \<longleftrightarrow>
      (match_iface (iiface m) (p_iiface p)) \<and>
      (match_iface (oiface m) (p_oiface p)) \<and>
      (simple_match_ip (src m) (p_src p)) \<and>
      (simple_match_ip (dst m) (p_dst p)) \<and>
      (simple_match_proto (proto m) (p_proto p)) \<and>
      (simple_match_port (sports m) (p_sport p)) \<and>
      (simple_match_port (dports m) (p_dport p))"

  fun simple_fw :: "simple_rule list \<Rightarrow> simple_packet \<Rightarrow> state" where
    "simple_fw [] _ = Undecided" |
    "simple_fw ((SimpleRule m Accept)#rs) p = (if simple_matches m p then Decision FinalAllow else simple_fw rs p)" |
    "simple_fw ((SimpleRule m Drop)#rs) p = (if simple_matches m p then Decision FinalDeny else simple_fw rs p)"


end

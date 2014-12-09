theory SimpleFwSyntax                                                                                                             
imports Main "../Bitmagic/IPv4Addr" "../Bitmagic/BitrangeLists" "../Output_Format/Negation_Type" "../Firewall_Common_Decision_State" String
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

  datatype iface = Iface "string negation_type" | IfaceAny
  
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
  text{*If the interface name ends in a "+", then any interface which begins with this name will match. (man iptables)*}
  fun cmp_iface_name :: "string \<Rightarrow> string \<Rightarrow> bool" where
    "cmp_iface_name [] [] \<longleftrightarrow> True" |
    "cmp_iface_name [i1] [] \<longleftrightarrow> (i1 = CHR ''+'')" |
    "cmp_iface_name [] [i2] \<longleftrightarrow> (i2 = CHR ''+'')" |
    "cmp_iface_name [i1] [i2] \<longleftrightarrow> (i1 = CHR ''+'' \<or> i2 = CHR ''+'' \<or> i1 = i2)" |
    "cmp_iface_name [i1] i2s \<longleftrightarrow> (i1 = CHR ''+'')" |
    "cmp_iface_name i1s [i2] \<longleftrightarrow> (i2 = CHR ''+'')" |
    "cmp_iface_name (i1#i1s) (i2#i2s) \<longleftrightarrow> (if i1 = i2 then cmp_iface_name i1s i2s else False)" |
    "cmp_iface_name _ _ \<longleftrightarrow> False"

  lemma cmp_iface_name_refl: "cmp_iface_name is is"
  proof -
  { fix i1 i2
    have "i1 = i2 \<Longrightarrow> cmp_iface_name i1 i2"
      by(induction i1 i2 rule: cmp_iface_name.induct)(auto)
   } thus ?thesis by simp 
  qed
  lemma cmp_iface_name_sym: "cmp_iface_name i1 i2 \<Longrightarrow> cmp_iface_name i2 i1"
    by(induction i1 i2 rule: cmp_iface_name.induct)(auto split: split_if_asm)

  lemma "cmp_iface_name (i2 # i2s) [] \<Longrightarrow> i2 = CHR ''+''"
  proof -
  assume a: "cmp_iface_name (i2 # i2s) []"
  { fix x1 x2
    have "x1 = (i2 # i2s) \<Longrightarrow> x2 = [] \<Longrightarrow> cmp_iface_name x1 x2 \<Longrightarrow> i2 = CHR ''+''"
    by(induction x1 x2 rule: cmp_iface_name.induct) (auto)
  } thus ?thesis using a by simp
  qed
  
  text{*Examples*}
    lemma cmp_iface_name_not_trans: "\<lbrakk>i1 = ''eth0''; i2 = ''eth+''; i3 = ''eth1''\<rbrakk> \<Longrightarrow> cmp_iface_name i1 i2 \<Longrightarrow> cmp_iface_name i2 i3 \<Longrightarrow> \<not> cmp_iface_name i1 i3"
      by(simp)
    lemma "cmp_iface_name ''+'' i2"
      by(induction "''+''" i2 rule: cmp_iface_name.induct) (simp_all)
    lemma "cmp_iface_name ''eth+'' ''eth3''" by eval
    lemma "cmp_iface_name ''eth+'' ''e+''" by eval
    lemma "cmp_iface_name ''eth+'' ''eth_tun_foobar''" by eval
    lemma "cmp_iface_name ''eth+'' ''eth_tun+++''" by eval
    lemma "\<not> cmp_iface_name ''eth+'' ''wlan+''" by eval
    lemma "cmp_iface_name ''eth1'' ''eth1''" by eval
    lemma "\<not> cmp_iface_name ''eth1'' ''eth2''" by eval
    text{*If the interfaces don't end in a wildcard, then @{const cmp_iface_name} is just simple equality*}
    lemma "\<lbrakk> hd (rev i1) \<noteq> CHR ''+''; hd (rev i2) \<noteq> CHR ''+'' \<rbrakk> \<Longrightarrow> cmp_iface_name i1 i2 \<longleftrightarrow> i1 = i2"
      apply(induction i1 i2 rule: cmp_iface_name.induct)
      apply(simp_all)
      apply (metis append_Nil hd_append2 list.sel(1))+
      done
      
  fun simple_match_iface :: "iface \<Rightarrow> string \<Rightarrow> bool" where
    "simple_match_iface IfaceAny p_iface \<longleftrightarrow> True" |
    "simple_match_iface (Iface (Pos i)) p_iface \<longleftrightarrow> cmp_iface_name p_iface i" |
    "simple_match_iface (Iface (Neg i)) p_iface \<longleftrightarrow> \<not> cmp_iface_name p_iface i"

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
      (simple_match_iface (iiface m) (p_iiface p)) \<and>
      (simple_match_iface (oiface m) (p_oiface p)) \<and>
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

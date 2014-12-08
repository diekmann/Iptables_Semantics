theory SimpleFwSyntax                                                                                                             
imports Main "../Bitmagic/IPv4Addr" "../Bitmagic/BitrangeLists" "../Output_Format/Negation_Type" "../Firewall_Common_Decision_State" String
begin


section{*Simple Packet*}
  text{*Packet constants are prefixed with p_*}
  datatype simple_packet_proto = p_TCP | p_UDP | p_ICMP | p_Other
  record simple_packet = p_iiface :: string
                         p_oiface :: string
                         p_src_ip :: ipv4addr
                         p_dst_ip :: ipv4addr
                         p_prot :: simple_packet_proto
                         p_sport :: "16 word"
                         p_dport :: "16 word"

section{*Simple Firewall Syntax (IPv4)*}
  datatype protocol = TCP | UDP | ICMP | ProtoAny

  datatype iface = Iface "string negation_type" | IfaceAny
  
  datatype simple_action = Accept | Drop
  
  (*TODO: can we get rid of the negation types? Or at least at the ports?*)
  record simple_match =
    iiface :: "iface" --"in-interface"
    oiface :: "iface" --"out-interface"
    src :: "(ipv4addr \<times> nat) negation_type" --"source"
    dst :: "(ipv4addr \<times> nat) negation_type" --"destination"
    prot :: "protocol negation_type"
    sports :: "(16 word \<times> 16 word) negation_type" --"source-port first:last"
    dports :: "(16 word \<times> 16 word) negation_type" --"destination-port first:last"

  datatype simple_rule = SimpleRule simple_match simple_action

section{*Simple Firewall Semantics*}
  (*TODO: iface wildcards:
    "If the interface name ends in a "+", then any interface which begins with this name will match."*)
  value "''+''"
  value "Char Nibble2 NibbleB"
  fun cmp_iface_name :: "string \<Rightarrow> string \<Rightarrow> bool" where
    "cmp_iface_name [] [] \<longleftrightarrow> True" |
    "cmp_iface_name [i1] [] \<longleftrightarrow> (i1 = CHR ''+'')" | (*TODO fixme*)
    "cmp_iface_name [i1] [i2] \<longleftrightarrow> (i1 = CHR ''+'' \<or> i2 = CHR ''+'' \<or> i1 = i2)" |
    "cmp_iface_name [i1] (i2#i22#i2s) \<longleftrightarrow> (i1 = CHR ''+'')" |
    "cmp_iface_name [] [i2] \<longleftrightarrow> (i2 = CHR ''+'')" |
    "cmp_iface_name (i1#i11#i1s) [i2] \<longleftrightarrow> (i2 = CHR ''+'')" |
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
    apply(induction i1 i2 rule: cmp_iface_name.induct)
    apply(auto split: split_if_asm)
    done

  lemma xxx: "cmp_iface_name (i2 # i2s) [] \<Longrightarrow> i2 = CHR ''+''"
  proof -
  assume a: "cmp_iface_name (i2 # i2s) []"
  { fix x1 x2
    have "x1 = (i2 # i2s) \<Longrightarrow> x2 = [] \<Longrightarrow> cmp_iface_name x1 x2 \<Longrightarrow> i2 = CHR ''+''"
    by(induction x1 x2 rule: cmp_iface_name.induct) (auto)
  } thus ?thesis using a by simp
  qed
    
  lemma cmp_iface_name_trans: "cmp_iface_name i1 i2 \<Longrightarrow> cmp_iface_name i2 i3 \<Longrightarrow> cmp_iface_name i1 i3"
  nitpick
  oops

  fun simple_match_iface :: "iface \<Rightarrow> string \<Rightarrow> bool" where
    "simple_match_iface IfaceAny p_iface \<longleftrightarrow> True" |
    "simple_match_iface (Iface (Pos i)) p_iface \<longleftrightarrow> p_iface = i" |
    "simple_match_iface (Iface (Neg i)) p_iface \<longleftrightarrow> p_iface \<noteq> i"

  fun simple_matches :: "simple_match \<Rightarrow> simple_packet \<Rightarrow> bool" where
    "simple_matches m p \<longleftrightarrow>
      (simple_match_iface (iiface m) (p_iiface p))"

  fun simple_fw :: "simple_rule list \<Rightarrow> state" where
    "simple_fw [] = Undecided" |
    "simple_fw (r#rs) = Undecided"


end

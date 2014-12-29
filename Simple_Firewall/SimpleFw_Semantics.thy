theory SimpleFw_Semantics
imports Main "../Bitmagic/IPv4Addr" "../Bitmagic/BitrangeLists" "../Output_Format/Negation_Type"
  "../Firewall_Common_Decision_State"
  "../Primitive_Matchers/Iface"
  "../Primitive_Matchers/Protocol"
  "../Primitive_Matchers/Simple_Packet"
begin


section{*Simple Firewall Syntax (IPv4)*}
text{*Very TODO*}
(*TODO*)


  datatype simple_action = Accept | Drop
  
  (*TODO: can we get rid of the negation types? Or at least at the ports?*)
  record simple_match =
    iiface :: "iface" --"in-interface"
    oiface :: "iface" --"out-interface"
    src :: "(ipv4addr \<times> nat) negation_type" --"source"
    dst :: "(ipv4addr \<times> nat) negation_type" --"destination"
    proto :: "protocol"
    sports :: "(16 word \<times> 16 word)" --"source-port first:last"
    dports :: "(16 word \<times> 16 word)" --"destination-port first:last"
    (*ports have no negation type as this can be represented by multiple firewall rules
      for example: !(3,4)
      is representable by
      (1,2) and (4,65535)
      *)

  datatype simple_rule = SimpleRule simple_match simple_action

subsection{*Simple Firewall Semantics*}

  fun simple_match_ip :: "(ipv4addr \<times> nat) negation_type \<Rightarrow> ipv4addr \<Rightarrow> bool" where
    "simple_match_ip (Pos (ip, n)) p_ip \<longleftrightarrow> p_ip \<in> ipv4range_set_from_bitmask ip n" |
    "simple_match_ip (Neg (ip, n)) p_ip \<longleftrightarrow> p_ip \<notin> ipv4range_set_from_bitmask ip n"

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
    "simple_match_any \<equiv> \<lparr>iiface=IfaceAny, oiface=IfaceAny, src=Pos (0,0), dst=Pos (0,0), proto=ProtoAny, sports=(0,65535), dports=(0,65535) \<rparr>"

  lemma simple_match_any: "simple_matches simple_match_any p"
    apply(simp add: simple_match_any_def ipv4range_set_from_bitmask_0)
    apply(subgoal_tac "(65535::16 word) = max_word")
     apply(simp)
    apply(simp add: max_word_def)
    done
    


end

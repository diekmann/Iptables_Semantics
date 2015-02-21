theory IPSpace_Syntax
imports Main String "../Bitmagic/IPv4Addr" "../Datatype_Selectors"
begin

section{*Primitive Matchers: IP Space Matcher*}

text{*Primitive Match Conditions which only support IPv4 addresses and layer 4 protocols.
Used to partition the IPv4 address space.
*}

(*IPT \<equiv> iptables*)

(*src dst ipv4*)
datatype ipt_ipv4range = Ip4Addr "nat \<times> nat \<times> nat \<times> nat"
                      | Ip4AddrNetmask "nat \<times> nat \<times> nat \<times> nat" nat -- "addr/xx"

datatype ipt_protocol = ProtAll | ProtTCP | ProtUDP

(*datatype ipt_ports = PortSingle nat | PortRange nat nat | PortMulti "ipt_ports list"*)

datatype_new iptrule_match = 
    is_Src: Src (src_range: ipt_ipv4range)
  | is_Dst: Dst (dst_range: ipt_ipv4range)
  | is_Prot: Prot (prot_sel: ipt_protocol)
  (*| Port ipt_ports*)
  | is_Extra: Extra (extra_sel: string)

(*datatype_compat iptrule_match*)


lemma wf_disc_sel_iptrule_match[simp]: 
      "wf_disc_sel (is_Src, src_range) Src"
      "wf_disc_sel (is_Dst, dst_range) Dst"
      "wf_disc_sel (is_Prot, prot_sel) Prot"
      "wf_disc_sel (is_Extra, extra_sel) Extra"
  by(simp_all add: wf_disc_sel.simps)


subsection{*Example Packet*}
  datatype protPacket = ProtTCP | ProtUDP
  record packet = src_ip :: ipv4addr
                  dst_ip :: ipv4addr
                  prot :: protPacket


hide_const (open) ProtTCP ProtUDP



fun ipv4s_to_set :: "ipt_ipv4range \<Rightarrow> ipv4addr set" where
  "ipv4s_to_set (Ip4AddrNetmask base m) = ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal base) m" |
  "ipv4s_to_set (Ip4Addr ip) = { ipv4addr_of_dotteddecimal ip }"

text{*@{term ipv4s_to_set} cannot represent an empty set.*}
lemma ipv4s_to_set_nonempty: "ipv4s_to_set ip \<noteq> {}"
  apply(cases ip)
   apply(simp)
  apply(simp add: ipv4range_set_from_bitmask_alt)
  apply(simp add: bitmagic_zeroLast_leq_or1Last)
  done

text{*maybe this is necessary as code equation?*}
lemma element_ipv4s_to_set: "addr \<in> ipv4s_to_set X = (
  case X of (Ip4AddrNetmask pre len) \<Rightarrow> ((ipv4addr_of_dotteddecimal pre) AND ((mask len) << (32 - len))) \<le> addr \<and> addr \<le> (ipv4addr_of_dotteddecimal pre) OR (mask (32 - len))
  | Ip4Addr ip \<Rightarrow> (addr = (ipv4addr_of_dotteddecimal ip)) )"
apply(cases X)
 apply(simp)
apply(simp add: ipv4range_set_from_bitmask_alt)
done




--"Misc"
(*we dont't have an empty ip space, but a space which only contains the 0 address. We will use the option type to denote the empty space in some functions.*)
lemma "ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal (0, 0, 0, 0)) 33 = {0}"
apply(simp add: ipv4addr_of_dotteddecimal.simps ipv4addr_of_nat_def)
apply(simp add: ipv4range_set_from_bitmask_def)
apply(simp add: ipv4range_set_from_netmask_def)
done


(*We need a separate ipv4addr syntax thy*)
 (*TODO: Move*)
 fun ipt_ipv4range_to_intervall :: "ipt_ipv4range \<Rightarrow> (ipv4addr \<times> ipv4addr)" where
    "ipt_ipv4range_to_intervall (Ip4Addr addr) = (ipv4addr_of_dotteddecimal addr, ipv4addr_of_dotteddecimal addr)" |
    "ipt_ipv4range_to_intervall (Ip4AddrNetmask pre len) = (
      let netmask = (mask len) << (32 - len);
          network_prefix = (ipv4addr_of_dotteddecimal pre AND netmask)
      in (network_prefix, network_prefix OR (NOT netmask))
     )" 

  
lemma ipt_ipv4range_to_intervall: "ipt_ipv4range_to_intervall ip = (s,e) \<Longrightarrow> {s .. e} = ipv4s_to_set ip"
  apply(cases ip)
   apply auto[1]
  apply(simp add: Let_def)
  apply(subst ipv4range_set_from_bitmask_alt)
  apply(subst(asm) NOT_mask_len32)
  by (metis NOT_mask_len32 ipv4range_set_from_bitmask_alt ipv4range_set_from_bitmask_alt1 ipv4range_set_from_netmask_def)


end

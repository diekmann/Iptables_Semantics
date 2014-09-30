theory IPSpace_Syntax
imports Main String "../Bitmagic/IPv4Addr"
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
term is_Src
term src_range


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


end

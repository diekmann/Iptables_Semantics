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

datatype iptrule_match = Src ipt_ipv4range | Dst ipt_ipv4range | Prot ipt_protocol (*| Port ipt_ports*) | Extra string



subsection{*Example Packet*}
  datatype protPacket = ProtTCP | ProtUDP
  record packet = src_ip :: ipv4addr
                  dst_ip :: ipv4addr
                  prot :: protPacket

(*TODO: ...*)
(*
  record packet_with_port = packet + port :: nat
*)

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




end

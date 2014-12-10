theory IPPortIfaceSpace_Syntax
imports Main String "../Bitmagic/IPv4Addr" "../Bitmagic/BitrangeLists" IPSpace_Syntax Protocol Iface Simple_Packet
begin

(*TODO: unify protocol types*)
hide_type(open) ipt_protocol
hide_const(open) ProtAll ProtTCP ProtUDP

section{*Primitive Matchers: Interfaces, IP Space, Layer 4 Ports Matcher*}

text{*Primitive Match Conditions which only support interfaces, IPv4 addresses,  layer 4 protocols, and layer 4 ports.
*}

(*list of (start, end) port ranges*)
type_synonym ipt_ports = "(16 word \<times> 16 word) list"


datatype ipport_rule_match = Src ipt_ipv4range | Dst ipt_ipv4range | IIface iface | OIface iface | Prot protocol | Src_Ports ipt_ports | Dst_Ports ipt_ports | Extra string



(*subsection{*Example Packet*}*)
 (*TODO: unify: packet + *)

  value "\<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotteddecimal (192,168,2,45), p_dst= ipv4addr_of_dotteddecimal (173,194,112,111),
         p_proto=TCP, p_sport=2065, p_dport=80\<rparr>"


fun ports_to_set :: "ipt_ports \<Rightarrow> (16 word) set" where
  "ports_to_set [] = {}" |
  "ports_to_set ((s,e)#ps) = {s..e} \<union> ports_to_set ps"

text{*We can reuse the bitrange theory to reason about ports*}
lemma ports_to_set_bitrange: "ports_to_set ps = bitrange_to_set (l2br ps)"
  by(induction ps) (auto)

end

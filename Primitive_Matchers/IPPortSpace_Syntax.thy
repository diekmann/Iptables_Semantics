theory IPPortSpace_Syntax
imports Main String "../Bitmagic/IPv4Addr" "../Bitmagic/BitrangeLists" IPSpace_Syntax
begin

section{*Primitive Matchers: IP Space and Layer 4 Ports Matcher*}

text{*Primitive Match Conditions which only support IPv4 addresses,  layer 4 protocols, and layer 4 ports.
*}

datatype ipt_protocol = ProtAll | ProtTCP | ProtUDP

(*list of (start, end) port ranges*)
type_synonym ipt_ports = "(16 word \<times> 16 word) list"

datatype ipport_rule_match = Src ipt_ipv4range | Dst ipt_ipv4range | Prot ipt_protocol | Src_Ports ipt_ports | Dst_Ports ipt_ports | Extra string



subsection{*Example Packet*}
  record packet_with_ports = packet +
        src_port :: "16 word"
        dst_port :: "16 word"

  value "\<lparr>src_ip = ipv4addr_of_dotteddecimal (192,168,2,45), dst_ip= ipv4addr_of_dotteddecimal (173,194,112,111),
         prot=protPacket.ProtTCP, src_port=2065, dst_port=80\<rparr>"




fun ports_to_set :: "ipt_ports \<Rightarrow> (16 word) set" where
  "ports_to_set [] = {}" |
  "ports_to_set ((s,e)#ps) = {s..e} \<union> ports_to_set ps"

text{*We can reuse the bitrange theory to reason about ports*}
lemma ports_to_set_bitrange: "ports_to_set ps = bitrange_to_set (l2br ps)"
  by(induction ps) (auto)

end
